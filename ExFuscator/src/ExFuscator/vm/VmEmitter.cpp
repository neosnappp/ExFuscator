/*

This file is a part of ExFuscator by kYro

>> https://github.com/neosnappp/ExFuscator/ <<

*/


#include "astra/vm/VmEmitter.hpp"
#include <chrono>
#include <cstdio>

#include "astra/NameGen.hpp"
#include "astra/vm/VmPack.hpp"

#include "astra/vm/Ed25519.hpp"
#include "astra/vm/LuaCryptoConsts.hpp"

#include <algorithm>
#include <array>
#include <cstdio>
#include <fstream>

#include "astra/vm/VmCrypto.hpp"

namespace astra {
namespace vm {

static std::string vmTexture(const std::string& in, Rng& rng) {
    auto idch = [](char x) {
        return (x >= 'a' && x <= 'z') || (x >= 'A' && x <= 'Z') ||
               (x >= '0' && x <= '9') || x == '_';
    };
    auto isKw = [](const std::string& t) {
        static const char* kws[] = {"and", "break", "do", "else", "elseif", "end",
            "false", "for", "function", "if", "in", "local", "nil", "not", "or",
            "repeat", "return", "then", "true", "until", "while"};
        for (const char* k : kws)
            if (t == k) return true;
        return false;
    };
    auto isEnder = [&](const std::string& t) {
        if (t.empty()) return false;
        if (t == "end" || t == "true" || t == "false" || t == "nil") return true;
        if (t == ")" || t == "]" || t == "}" || t == "\"") return true;
        if (t[0] == '"' || t[0] == '\'') return true;
        if (!isKw(t) && idch(t[0])) return true;
        return false;
    };
    std::string o;
    o.reserve(in.size() * 2);
    std::vector<char> st;
    std::string prev = "\x01";
    bool exprDone = false;
    bool cap = false;
    size_t baseFrames = 0;
    std::string rhs;
    size_t i = 0, n = in.size();
    auto blkTop = [&]() {
        if (st.empty()) return true;
        char t = st.back();
        return t == 'F' || t == 'D' || t == 'T' || t == 'R';
    };
    auto atBase = [&]() {
        return cap && blkTop() && st.size() == baseFrames && exprDone;
    };
    auto put = [&](const std::string& s) {
        if (cap) rhs += s; else o += s;
    };
    auto flushRhs = [&]() {
        if (!cap || rhs.empty()) { cap = false; rhs.clear(); return; }
        cap = false;
        int dep = 2;
        int r = (int)rng.range(100);
        if (r < 18) dep = 3;
        else if (r >= 94) dep = 1;
        for (int q = 0; q < dep; ++q) o += '(';
        o += rhs;
        for (int q = 0; q < dep; ++q) o += ')';
        rhs.clear();
        prev = ")";
        exprDone = true;
    };
    auto insertSep = [&]() {
        if (!cap && blkTop() && isEnder(prev) && !o.empty()) {
            o += ';';
            prev = ";";
        }
    };
    auto skipWs = [&](size_t from) {
        size_t j = from;
        while (j < n && (in[j] == ' ' || in[j] == '\t' || in[j] == '\r' || in[j] == '\n')) ++j;
        return j;
    };
    auto nextNw = [&](size_t from) {
        size_t j = skipWs(from);
        return j < n ? in[j] : (char)0;
    };

    static const std::string kCryB = "\"\\251\\252\\249\\248\"";
    static const std::string kCryE = "\"\\247\\246\\245\\244\"";
    while (i < n) {
        if (in.compare(i, kCryB.size(), kCryB) == 0) {
            size_t j = in.find(kCryE, i + kCryB.size());
            if (j == std::string::npos) j = n; else j += kCryE.size();
            flushRhs();
            cap = false;
            rhs.clear();
            o.append(in, i, j - i);
            i = j;
            exprDone = true;
            prev = "\"";
            continue;
        }
        char c = in[i];
        if (c == '"' || c == '\'') {
            size_t j = i + 1;
            while (j < n) {
                if (in[j] == '\\') { j += 2; continue; }
                if (in[j] == c) { ++j; break; }
                ++j;
            }
            if (j > n) j = n;
            put(in.substr(i, j - i));
            i = j;
            exprDone = true;
            prev = "\"";
            continue;
        }
        if (idch(c)) {
            size_t j = i;
            while (j < n && idch(in[j])) ++j;
            std::string tok = in.substr(i, j - i);
            i = j;
            if (tok == "function") {
                if (atBase()) flushRhs();
                insertSep();
                put("function");
                st.push_back('F');
                size_t j = skipWs(i);
                if (!(j < n && in[j] == '(')) {
                    while (j < n && (idch(in[j]) || in[j] == '.' || in[j] == ':')) ++j;
                    j = skipWs(j);
                }
                if (j < n && in[j] == '(') {
                    int d = 0;
                    while (j < n) {
                        if (in[j] == '(') ++d;
                        else if (in[j] == ')') { --d; ++j; if (d == 0) break; continue; }
                        ++j;
                    }
                }
                put(in.substr(i, j - i));
                i = j;
                exprDone = false;
                prev = "\x02";
                continue;
            }
            if (tok == "local") {
                if (atBase()) flushRhs();
                insertSep();
                put("local");
                size_t j = skipWs(i);
                int names = 0;
                bool eq = false;
                bool kwName = false;
                size_t rhsStart = n;
                size_t j2 = j;
                while (j2 < n && idch(in[j2])) {
                    size_t k = j2;
                    while (k < n && idch(in[k])) ++k;
                    std::string nm = in.substr(j2, k - j2);
                    if (isKw(nm)) { kwName = true; break; }
                    ++names;
                    size_t j3 = skipWs(k);
                    if (j3 < n && in[j3] == ',') { j2 = skipWs(j3 + 1); continue; }
                    if (j3 < n && in[j3] == '=' && (j3 + 1 >= n || in[j3 + 1] != '=')) {
                        eq = true;
                        rhsStart = skipWs(j3 + 1);
                    }
                    break;
                }
                if (!kwName && eq && names == 1 && !cap) {
                    put(in.substr(i, rhsStart - i));
                    cap = true;
                    baseFrames = st.size();
                    rhs.clear();
                    i = rhsStart;
                } else {
                    if (j > i) put(in.substr(i, j - i));
                    i = j;
                }
                exprDone = false;
                prev = "\x02";
                continue;
            }
            if (tok == "if" || tok == "while" || tok == "for" || tok == "repeat" ||
                tok == "return" || tok == "break" || tok == "continue") {
                if (atBase()) flushRhs();
                insertSep();
                put(tok);
                if (tok == "repeat") st.push_back('R');
                if (tok == "while" || tok == "for") st.push_back('W');
                exprDone = false;
                prev = tok;
                continue;
            }
            if (tok == "then") {
                st.push_back('T');
                put(tok);
                exprDone = false;
                prev = tok;
                continue;
            }
            if (tok == "do") {
                if (!st.empty() && st.back() == 'W') {
                    st.pop_back();
                    put(tok);
                    st.push_back('D');
                } else {
                    if (atBase()) flushRhs();
                    insertSep();
                    st.push_back('D');
                    put(tok);
                }
                exprDone = false;
                prev = tok;
                continue;
            }
            if (tok == "else") {
                if (!st.empty() && st.back() == 'T') { st.pop_back(); st.push_back('T'); }
                put(tok);
                exprDone = false;
                prev = tok;
                continue;
            }
            if (tok == "elseif") {
                if (!st.empty() && st.back() == 'T') st.pop_back();
                put(tok);
                exprDone = false;
                prev = tok;
                continue;
            }
            if (tok == "until") {
                if (!st.empty() && st.back() == 'R') st.pop_back();
                put(tok);
                exprDone = false;
                prev = tok;
                continue;
            }
            if (tok == "end") {
                if (cap) {
                    rhs += "end";
                    if (!st.empty() && (st.back() == 'F' || st.back() == 'D' || st.back() == 'T'))
                        st.pop_back();
                    exprDone = true;
                    if (atBase()) flushRhs();
                    else prev = "end";
                    continue;
                }
                put("end");
                if (!st.empty() && (st.back() == 'F' || st.back() == 'D' || st.back() == 'T'))
                    st.pop_back();
                char nc = nextNw(i);
                if (nc != ')' && nc != '}' && nc != ']' && nc != ',' && nc != ';' &&
                    nc != '.' && nc != ':' && nc != 0) {
                    o += ';';
                    prev = ";";
                } else {
                    prev = "end";
                }
                continue;
            }
            if (tok == "and" || tok == "or" || tok == "not" || tok == "in") {
                put(tok);
                exprDone = false;
                prev = tok;
                continue;
            }
            if (atBase()) flushRhs();
            insertSep();
            put(tok);
            exprDone = true;
            prev = tok;
            continue;
        }
        char c2 = (i + 1 < n) ? in[i + 1] : (char)0;
        std::string tok;
        size_t nl = 1;
        if (c == '.' && c2 == '.' && i + 2 < n && in[i + 2] == '.') {
            tok = "...";
            nl = 3;
        } else if ((c == '=' && c2 == '=') || (c == '~' && c2 == '=') ||
                   (c == '<' && c2 == '=') || (c == '>' && c2 == '=')) {
            tok = in.substr(i, 2);
            nl = 2;
        } else if (c == '.' && c2 == '.') {
            tok = "..";
            nl = 2;
        } else {
            tok = std::string(1, c);
        }
        i += nl;
        if (tok == "," || tok == ";") {
            if (atBase()) flushRhs();
            put(tok);
            exprDone = false;
            prev = tok;
            continue;
        }
        if (tok == "(") { st.push_back('P'); put(tok); exprDone = false; prev = tok; continue; }
        if (tok == "[") { st.push_back('B'); put(tok); exprDone = false; prev = tok; continue; }
        if (tok == "{") { st.push_back('C'); put(tok); exprDone = false; prev = tok; continue; }
        if (tok == ")") {
            if (!st.empty() && st.back() == 'P') st.pop_back();
            put(tok);
            exprDone = true;
            prev = tok;
            continue;
        }
        if (tok == "]") {
            if (!st.empty() && st.back() == 'B') st.pop_back();
            put(tok);
            exprDone = true;
            prev = tok;
            continue;
        }
        if (tok == "}") {
            if (!st.empty() && st.back() == 'C') st.pop_back();
            put(tok);
            exprDone = true;
            prev = tok;
            continue;
        }
        if (tok.size() == 1 && (tok[0] == ' ' || tok[0] == '\n' || tok[0] == '\t' || tok[0] == '\r')) {
            put(tok);
            continue;
        }
        put(tok);
        exprDone = (tok == "...");
        prev = tok;
        continue;
    }
    if (cap) flushRhs();
    return o;
}

std::string emitVmOutput(const VmBuild& b, std::uint64_t seed,
                         const std::string& watermark) {
    Rng rng(seed ^ 0xE11177ULL);
    std::unordered_set<std::string> tmplNames = {
        "t1", "t2", "t3", "t4", "i", "j", "x", "y", "st", "s", "h", "g", "e",
        "v", "P", "fr", "tp", "vo", "rg", "c", "id", "sc", "key", "src", "buf",
        "d", "cur", "r1", "r2", "r4", "np", "va", "nu", "nr", "nk", "nc", "ni",
        "nf", "kd", "ix", "uvs", "ks", "kse", "ty", "ln", "el", "pl", "kids",
        "code", "op", "L", "a", "b", "k", "m", "fl", "stt", "pp", "args", "r",
        "pc", "tk", "ins", "out", "rs", "off", "rt", "ar", "\119", "cp", "cells",
        "ds", "c0", "cb", "pos", "n", "l", "mc", "mg", "mp", "m0", "e0", "t",
        "uv", "f", "ds", "o", "md", "rl", "cl", "tkn", "ll", "ml", "kb", "gi",
        "cnt", "q1", "q2", "alpha", "hd", "h2", "s1"
    };
    static const char* extraList[] = {
        "m1", "m2", "dm", "ord", "pv", "pq", "f0", "acc", "lnT", "ofT",
        "rwT", "vs0", "pc2", "j2", "mj", "wa", "wb", "kk", "cd", "sa", "jt",
        "sb", "z", "z2", "pk", "kt", "\113", "mr", "ws", "wj", "zz", "P2",
        "pi", "R", "base", "s0", "s2", "c4", "c5", "a8", "b16", "c8",
        "jm", "b3", "s3", "n5", "q0", "pg", "vk", "vb", "px", "p", "lv",
        "tot", "ac", "rws", "ckv", "nj", "ji", "jv", "t0", "h1", "h2",
        "h3", "key2", "wv2", "wq2", "ws2", "fk", "tv", "nv", "tw", "qx",
        "qy", "qz", "s5", "m6", "b2v", "c2v", "sv", "kv", "w0", "mp",
        "vs", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8", "b1", "b2",
        "b4", "b5", "b6", "b7", "b8", "c1", "c2", "c3", "MR",
        "kk2", "kk3", "kv2", "kv3", "Pq", "kc", "qd",
        "afa", "afb", "afi", "abq", "aeq", "asq", "zc3", "zo3", "mt", "vt",
        "pf", "pn", "lb", "ps4", "x5", "y5", "w1", "w2", "w3", "w4", "w5",
        "w6", "w7", "w8", "qp", "s2", "v9"
    };
    for (const char* exn : extraList) tmplNames.insert(exn);
    std::string tmplT = R"TMPL(
local @K31@=@E31@ local @K31B@=@E31B@ local @K31H@=@E31H@ local @K32@=@E32@
local @K24@=@E24@ local @K23@=@E23@ local @K16@=@E16@
local @ENV@=getfenv and getfenv(1) or _G
local @STR@,@MTH@,@TBL@,@SEL@,@BYT@,@CHR@,@SUB@,@CAT@,@FLR@,@UPK@,@SLN@,@SRP@
@JK1@
local @ERR@=@ENV@["\101\114\114\111\114"]
local function @WP@() @ERR@("\069\088\070\049",0) end
if type(@ENV@)~="table" then @WP@() end
@STR@=@ENV@["\115\116\114\105\110\103"] @MTH@=@ENV@["\109\097\116\104"] @TBL@=@ENV@["\116\097\098\108\101"]
if type(@STR@)~="table" or type(@MTH@)~="table" or type(@TBL@)~="table" then @WP@() end
@BYT@=@STR@.byte @CHR@=@STR@.char @SUB@=@STR@.sub @SLN@=@STR@.len @SRP@=@STR@.rep @CAT@=@TBL@.concat @FLR@=@MTH@.floor
if type(@BYT@)~="function" or type(@CHR@)~="function" or type(@SUB@)~="function" or type(@SLN@)~="function" or type(@SRP@)~="function" or type(@CAT@)~="function" or type(@FLR@)~="function" then @WP@() end
if @BYT@("\065\090",1)~=65 or @BYT@("\065\090",2)~=90 or @SUB@("\097\113\119\122",2,3)~="\113\119" or @CHR@(88)~="\088" or @SLN@("\097\113\055")~=3 or @SRP@("\107\050",3)~="\107\050\107\050\107\050" or @FLR@(9.7)~=9 or @FLR@(-0.5)~=-1 then @WP@() end
local @XT@={}
for t1=0,15 do @XT@[t1]={} for t2=0,15 do local t3=0 for t4=0,3 do t3=t3+((@FLR@(t1/2^t4)%2+@FLR@(t2/2^t4)%2)%2)*2^t4 end @XT@[t1][t2]=t3 end end
local function @BX@(x,y) return @XT@[x%16][y%16]+16*@XT@[@FLR@(x/16)%16][@FLR@(y/16)%16] end
local function @KX@(x,y) return @BX@(x%256,y%256)+256*@BX@(@FLR@(x/256)%256,@FLR@(y/256)%256)+65536*@BX@(@FLR@(x/65536)%256,@FLR@(y/65536)%256)+16777216*@BX@(@FLR@(x/16777216),@FLR@(y/16777216)) end
local @AT@={} local @OT@={}
for t1=0,15 do @AT@[t1]={} @OT@[t1]={} for t2=0,15 do local t3=0 local t4b=0 for t5=0,3 do local ba=@FLR@(t1/2^t5)%2 local bb=@FLR@(t2/2^t5)%2 t3=t3+ba*bb*2^t5 t4b=t4b+(ba+bb-ba*bb)*2^t5 end @AT@[t1][t2]=t3 @OT@[t1][t2]=t4b end end
local function @A8@(x,y) return @AT@[x%16][y%16]+16*@AT@[@FLR@(x/16)%16][@FLR@(y/16)%16] end
local function @O8@(x,y) return @OT@[x%16][y%16]+16*@OT@[@FLR@(x/16)%16][@FLR@(y/16)%16] end
local function @ANDF@(x,y) return @A8@(x%256,y%256)+256*@A8@(@FLR@(x/256)%256,@FLR@(y/256)%256)+65536*@A8@(@FLR@(x/65536)%256,@FLR@(y/65536)%256)+16777216*@A8@(@FLR@(x/16777216),@FLR@(y/16777216)) end
local function @ORF@(x,y) return @O8@(x%256,y%256)+256*@O8@(@FLR@(x/256)%256,@FLR@(y/256)%256)+65536*@O8@(@FLR@(x/65536)%256,@FLR@(y/65536)%256)+16777216*@O8@(@FLR@(x/16777216),@FLR@(y/16777216)) end
local function @X8@(x,y) return @XT@[x%16][y%16]+16*@XT@[@FLR@(x/16)%16][@FLR@(y/16)%16] end
local function @XRF@(x,y) return @X8@(x%256,y%256)+256*@X8@(@FLR@(x/256)%256,@FLR@(y/256)%256)+65536*@X8@(@FLR@(x/65536)%256,@FLR@(y/65536)%256)+16777216*@X8@(@FLR@(x/16777216),@FLR@(y/16777216)) end
-- ====== EXF-02 pure-Lua crypto (SHA-512 + Ed25519 verify) BEGIN ======
local s5mb="\251\252\249\248"
local @S512@, @E5V@
do

 -- ======================================================================
 -- Pure-Lua SHA-512 + Ed25519 verify (doubles only; Lua 5.1 / Luau safe)
 -- ======================================================================
 local e5p={16777197,16777215,16777215,16777215,16777215,16777215,16777215,16777215,16777215,16777215,32767}
 local e5p2={16777178,16777215,16777215,16777215,16777215,16777215,16777215,16777215,16777215,16777215,65535}
 local e5d={5863587,5098003,11236843,4276696,7342669,15243264,7960441,9226048,7339635,7138859,20995}
 local e5i={958640,1779530,7914734,11349988,4397062,14133039,10042875,2837760,12705547,2392143,11139}
 local e5g={6710872,6710886,6710886,6710886,6710886,6710886,6710886,6710886,6710886,6710886,26214}
 local e5L={16110573,6494812,14047250,10680220,14612958,20,0,0,0,0,4096}
 local e5ei={16777195,16777215,16777215,16777215,16777215,16777215,16777215,16777215,16777215,16777215,32767}
 local e5es={16777214,16777215,16777215,16777215,16777215,16777215,16777215,16777215,16777215,16777215,4095}
 local e5gx={2479386,2973839,11716950,9774503,2934624,14441577,3276246,12625122,7230462,3593165,8553}
 local e5gt={12049827,9089957,16084446,7819602,15769472,14908704,9331883,6744654,9139813,6229975,26503}
 local e5z={0,0,0,0,0,0,0,0,0,0,0}
 local e5o={1,0,0,0,0,0,0,0,0,0,0}
 local e5B={e5gx,e5g,e5o,e5gt}
 local function e5gep(t)
  if t[11]>32767 then return true end
  if t[11]<32767 then return false end
  for i=10,2,-1 do
   if t[i]~=16777215 then return t[i]>16777215 end
  end
  return t[1]>=16777197
 end
 local function e5can(t)
  local cr=0
  for i=1,11 do local v=t[i]+cr t[i]=v%16777216 cr=@FLR@(v/16777216) end
  while cr>0 or t[11]>=32768 do
   if cr>0 then t[1]=t[1]+9728*cr cr=0 end
   if t[11]>=32768 then
    local hi=@FLR@(t[11]/32768) t[11]=t[11]%32768 t[1]=t[1]+19*hi
   end
   for i=1,11 do local v=t[i]+cr t[i]=v%16777216 cr=@FLR@(v/16777216) end
  end
  while e5gep(t) do
   t[1]=t[1]-16777197
   for i=2,10 do t[i]=t[i]-16777215 end
   t[11]=t[11]-32767
  end
  return t
 end
 local function e5mul(a,b)
  local c={}
  for i=1,26 do c[i]=0 end
  for i=1,11 do
   local ai=a[i]
   if ai~=0 then
    for j=1,11 do c[i+j-1]=c[i+j-1]+ai*b[j] end
   end
  end
  local cr=0
  for i=1,26 do local v=c[i]+cr c[i]=v%16777216 cr=@FLR@(v/16777216) end
  for k=12,26 do
   local v=c[k]
   if v>0 then
    local pos=24*(k-1)
    local q=@FLR@(pos/255)
    local r=pos-255*q
    local cf=1
    if q==1 then cf=19 elseif q==2 then cf=361 end
    c[@FLR@(r/24)+1]=c[@FLR@(r/24)+1]+cf*v*2^(r%24)
   end
  end
  cr=0
  for i=1,11 do local v=c[i]+cr c[i]=v%16777216 cr=@FLR@(v/16777216) end
  while cr>0 or c[11]>=32768 do
   if cr>0 then c[1]=c[1]+9728*cr cr=0 end
   if c[11]>=32768 then
    local hi=@FLR@(c[11]/32768) c[11]=c[11]%32768 c[1]=c[1]+19*hi
   end
   for i=1,11 do local v=c[i]+cr c[i]=v%16777216 cr=@FLR@(v/16777216) end
  end
  return c
 end
 local function e5add(a,b)
  local t={}
  for i=1,11 do t[i]=a[i]+b[i] end
  local cr=0
  for i=1,11 do local v=t[i]+cr t[i]=v%16777216 cr=@FLR@(v/16777216) end
  while cr>0 or t[11]>=32768 do
   if cr>0 then t[1]=t[1]+9728*cr cr=0 end
   if t[11]>=32768 then
    local hi=@FLR@(t[11]/32768) t[11]=t[11]%32768 t[1]=t[1]+19*hi
   end
   for i=1,11 do local v=t[i]+cr t[i]=v%16777216 cr=@FLR@(v/16777216) end
  end
  return t
 end
 local function e5sub(a,b)
  local t={}
  for i=1,11 do t[i]=a[i]-b[i]+e5p2[i] end
  local cr=0
  for i=1,11 do local v=t[i]+cr t[i]=v%16777216 cr=@FLR@(v/16777216) end
  while cr>0 or t[11]>=32768 do
   if cr>0 then t[1]=t[1]+9728*cr cr=0 end
   if t[11]>=32768 then
    local hi=@FLR@(t[11]/32768) t[11]=t[11]%32768 t[1]=t[1]+19*hi
   end
   for i=1,11 do local v=t[i]+cr t[i]=v%16777216 cr=@FLR@(v/16777216) end
  end
  return t
 end
 local function e5sq(a) return e5mul(a,a) end
 local function e5neg(a) return e5sub(e5z,a) end
 local function e5bit(t,i) return @FLR@(t[@FLR@(i/24)+1]/2^(i%24))%2 end
 local function e5eq(a,b)
  local x=e5can({a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8],a[9],a[10],a[11]})
  local y=e5can({b[1],b[2],b[3],b[4],b[5],b[6],b[7],b[8],b[9],b[10],b[11]})
  for i=1,11 do if x[i]~=y[i] then return false end end
  return true
 end
 local function e5pow(base,exp)
  local r=e5o
  for i=254,0,-1 do
   r=e5sq(r)
   if e5bit(exp,i)==1 then r=e5mul(r,base) end
  end
  return e5can(r)
 end
 local function e5inv(a) return e5pow(a,e5ei) end
 local function e5decb(b)
  local t={0,0,0,0,0,0,0,0,0,0,0}
  for i=0,29 do
   local q=@FLR@(i/3)+1
   t[q]=t[q]+@BYT@(b,i+1)*2^(8*(i%3))
  end
  t[11]=@BYT@(b,31)+(@BYT@(b,32)%128)*256
  local sign=@FLR@(@BYT@(b,32)/128)%2
  e5can(t)
  return t,sign
 end
 local function e5xrec(y)
  local yy=e5sq(y)
  local u=e5sub(yy,e5o)
  local v=e5add(e5mul(e5d,yy),e5o)
  local x=e5mul(u,e5inv(v))
  x=e5pow(x,e5es)
  local chk=e5mul(e5sq(x),v)
  if not e5eq(chk,u) then
   if e5eq(chk,e5neg(u)) then x=e5mul(x,e5i)
   else return nil end
  end
  if x[1]%2==1 then x=e5neg(x) end
  return x
 end
 local function e5dec(b)
  local y,sign=e5decb(b)
  local x=e5xrec(y)
  if not x then return nil end
  if x[1]%2~=sign then x=e5neg(x) end
  return {x,y,e5o,e5mul(x,y)}
 end
 local function e5cmp(P)
  local zi=e5inv(P[3])
  local x=e5can(e5mul(P[1],zi))
  local y=e5can(e5mul(P[2],zi))
  local o={}
  for i=0,29 do o[i+1]=@CHR@(@FLR@(y[@FLR@(i/3)+1]/2^(8*(i%3)))%256) end
  o[31]=@CHR@(y[11]%256)
  o[32]=@CHR@(@FLR@(y[11]/256)+(x[1]%2)*128)
  return @CAT@(o)
 end
 local function e5addp(P,Q)
  local A=e5mul(e5sub(P[2],P[1]),e5sub(Q[2],Q[1]))
  local Bv=e5mul(e5add(P[2],P[1]),e5add(Q[2],Q[1]))
  local C=e5mul(P[4],Q[4]) C=e5add(C,C) C=e5mul(C,e5d)
  local Dv=e5mul(P[3],Q[3]) Dv=e5add(Dv,Dv)
  local E=e5sub(Bv,A)
  local F=e5sub(Dv,C)
  local G=e5add(Dv,C)
  local H=e5add(Bv,A)
  return {e5mul(E,F),e5mul(G,H),e5mul(F,G),e5mul(E,H)}
 end
 local function e5dbl(P)
  local X,Y,Z=P[1],P[2],P[3]
  local A=e5sq(X)
  local Bv=e5sq(Y)
  local zs=e5sq(Z)
  local C=e5add(zs,zs)
  local D=e5neg(A)
  local E=e5sq(e5add(X,Y))
  E=e5sub(E,A) E=e5sub(E,Bv)
  local G=e5add(D,Bv)
  local F=e5sub(G,C)
  local H=e5sub(D,Bv)
  return {e5mul(E,F),e5mul(G,H),e5mul(F,G),e5mul(E,H)}
 end
 local function e5muls(P,s)
  local R={e5z,e5o,e5o,e5z}
  for i=254,0,-1 do
   R=e5dbl(R)
   if e5bit(s,i)==1 then R=e5addp(R,P) end
  end
  return R
 end
 local function e5ltl(a,b)
  for i=11,1,-1 do
   if a[i]~=b[i] then return a[i]<b[i] end
  end
  return false
 end
 local function e5modL(h)
  local c={}
  for i=1,22 do c[i]=0 end
  for i=0,63 do
   local q=@FLR@(i/3)+1
   c[q]=c[q]+@BYT@(h,i+1)*2^(8*(i%3))
  end
  local acc={0,0,0,0,0,0,0,0,0,0,0}
  for i=527,0,-1 do
   local cr=e5bit(c,i)
   for j=1,11 do
    local v=acc[j]*2+cr
    acc[j]=v%16777216
    cr=@FLR@(v/16777216)
   end
   if not e5ltl(acc,e5L) then
    local br=0
    for j=1,11 do
     local v=acc[j]-e5L[j]+br
     if v<0 then v=v+16777216 br=-1 else br=0 end
     acc[j]=v
    end
   end
  end
  return acc
 end
 -- ---------------------------------------------------------------- SHA-512
 local e5kl,e5kh={}, {}
 do
  local n=1
  local s5k="@S5KC@"
  for v in s5k:gmatch("[0-9]+") do
   local x=tonumber(v)
   if n%2==1 then e5kh[@FLR@(n/2)+1]=x else e5kl[@FLR@(n/2)]=x end
   n=n+1
  end
 end
 local E5DW,E5DWL,E5DA,E5DAH,E5DR,E5DC,E5DB={}, {}, {}, {}, {}, {}, {}
 local DBG=false
 @S512@=function(msg)
  local n=#msg
  local blocks=@FLR@((n+17+127)/128)
  local padded=blocks*128
  local B={}
  do
   local i=1
   while i<=n do
    local j=i+4095
    if j>n then j=n end
    local part={@BYT@(msg,i,j)}
    for k2=1,j-i+1 do B[i+k2-1]=part[k2] end
    i=j+1
   end
  end
  B[n+1]=128
  for i=n+2,padded do B[i]=0 end
  local bl=n*8
  for i=0,7 do B[padded-i]=@FLR@(bl/2^(8*i))%256 end
  local a0,e5a1,b0,e5b1,c0,e5c1,d0,e5d1=4089235720,1779033703, 2227873595,3144134277, 4271175723,1013904242, 1595750129,2773480762
  local e0,e5e1,f0,e5f1,g0,e5g1,h0,e5h1=2917565137,1359893119, 725511199,2600822924, 4215389547,528734635, 327033209,1541459225
  for blk=0,blocks-1 do
   local base=blk*128
   local wl,wh={}, {}
   for t=0,15 do
    local o=base+t*8
    wh[t]=B[o+1]*16777216+B[o+2]*65536+B[o+3]*256+B[o+4]
    wl[t]=B[o+5]*16777216+B[o+6]*65536+B[o+7]*256+B[o+8]
   end
   local s5va,s5vah,s5vb,s5vbh,s5vc,s5vch,s5vd,s5vdh=a0,e5a1,b0,e5b1,c0,e5c1,d0,e5d1
   local s5ve,s5veh,s5vf,s5vfh,s5vg,s5vgh,s5vh,s5vhh=e0,e5e1,f0,e5f1,g0,e5g1,h0,e5h1
   for t=16,79 do
    local x2l,x2h=wl[t-2],wh[t-2]
    local r1l=@FLR@(x2l/524288)+(x2h%524288)*8192
    local r1h=@FLR@(x2h/524288)
    local o1h=(x2l%524288)*8192
    local s1h=@XRF@(r1h,o1h)
    local s1l=r1l
    local r2l=@FLR@(x2h/536870912)
    local o2l=(x2l%536870912)*8
    local o2h=((x2h%536870912)*8+@FLR@(x2l/536870912))%4294967296
    s1l=@XRF@(s1l,@XRF@(r2l,o2l))
    s1h=@XRF@(s1h,o2h)
    local r6l=@FLR@(x2l/64)+(x2h%64)*67108864
    local r6h=@FLR@(x2h/64)
    s1l=@XRF@(s1l,r6l)
    s1h=@XRF@(s1h,r6h)
    local x7l,x7h=wl[t-15],wh[t-15]
    local q1l=@FLR@(x7l/2)+(x7h%2)*2147483648
    local q1h=@FLR@(x7h/2)
    local w1h=(x7l%2)*2147483648
    local s0h=@XRF@(q1h,w1h)
    local s0l=q1l
    local q8l=@FLR@(x7l/256)+(x7h%256)*16777216
    local q8h=@FLR@(x7h/256)
    local w8h=(x7l%256)*16777216
    s0l=@XRF@(s0l,q8l)
    s0h=@XRF@(s0h,@XRF@(q8h,w8h))
    local q7l=@FLR@(x7l/128)+(x7h%128)*33554432
    local q7h=@FLR@(x7h/128)
    s0l=@XRF@(s0l,q7l)
    s0h=@XRF@(s0h,q7h)
    local sl=s1l+wl[t-7]
    local sh=s1h+wh[t-7]+@FLR@(sl/4294967296)
    sl=sl%4294967296
    sl=sl+s0l
    sh=sh+s0h+@FLR@(sl/4294967296)
    sl=sl%4294967296
    sl=sl+wl[t-16]
    sh=sh+wh[t-16]+@FLR@(sl/4294967296)
    wl[t]=sl%4294967296
    wh[t]=sh%4294967296
   end
   if DBG and blk<=1 then
    for t=0,79 do E5DW[blk*80+t]=wh[t] E5DWL[blk*80+t]=wl[t] end
   end
   for t=0,79 do
    local xl,xh=e0,e5e1
    local r1l=@FLR@(xl/16384)+(xh%16384)*262144
    local r1h=@FLR@(xh/16384)
    local o1h=(xl%16384)*262144
    local bsh1h=@XRF@(r1h,o1h)
    local bsh1l=r1l
    local r2l=@FLR@(xl/262144)+(xh%262144)*16384
    local r2h=@FLR@(xh/262144)
    local o2h=(xl%262144)*16384
    bsh1l=@XRF@(bsh1l,r2l)
    bsh1h=@XRF@(bsh1h,@XRF@(r2h,o2h))
    local r6l=@FLR@(xh/512)
    local o6l=(xl%512)*8388608
    local o6h=((xh%512)*8388608+@FLR@(xl/512))%4294967296
    bsh1l=@XRF@(bsh1l,@XRF@(r6l,o6l))
    bsh1h=@XRF@(bsh1h,o6h)
    local chl=@XRF@(@ANDF@(e0,f0),@ANDF@(4294967295-e0,g0))
    local chh=@XRF@(@ANDF@(e5e1,e5f1),@ANDF@(4294967295-e5e1,e5g1))
    local t1l=h0+bsh1l
    local t1h=e5h1+bsh1h+@FLR@(t1l/4294967296)
    t1l=t1l%4294967296
    t1l=t1l+chl
    t1h=t1h+chh+@FLR@(t1l/4294967296)
    t1l=t1l%4294967296
    t1l=t1l+e5kl[t+1]
    t1h=t1h+e5kh[t+1]+@FLR@(t1l/4294967296)
    t1l=t1l%4294967296
    t1l=t1l+wl[t]
    t1h=t1h+wh[t]+@FLR@(t1l/4294967296)
    t1l=t1l%4294967296
    t1h=t1h%4294967296
    local al,ah=a0,e5a1
    local q1l=@FLR@(al/268435456)+(ah%268435456)*16
    local q1h=@FLR@(ah/268435456)
    local w1h=(al%268435456)*16
    local bsh0h=@XRF@(q1h,w1h)
    local bsh0l=q1l
    local q8l=@FLR@(ah/4)
    local w8l=(al%4)*1073741824
    local w8h=((ah%4)*1073741824+@FLR@(al/4))%4294967296
    bsh0l=@XRF@(bsh0l,@XRF@(q8l,w8l))
    bsh0h=@XRF@(bsh0h,w8h)
    local q7l=@FLR@(ah/128)
    local w7l=(al%128)*33554432
    local w7h=((ah%128)*33554432+@FLR@(al/128))%4294967296
    bsh0l=@XRF@(bsh0l,@XRF@(q7l,w7l))
    bsh0h=@XRF@(bsh0h,w7h)
    if DBG and blk==0 and t==0 then
     E5DC[1]=bsh1h E5DC[2]=bsh1l E5DC[3]=bsh0h E5DC[4]=bsh0l E5DC[5]=chh E5DC[6]=chl E5DC[7]=t1h E5DC[8]=t1l
    end
    local mjl=@XRF@(@XRF@(@ANDF@(a0,b0),@ANDF@(a0,c0)),@ANDF@(b0,c0))
    local mjh=@XRF@(@XRF@(@ANDF@(e5a1,e5b1),@ANDF@(e5a1,e5c1)),@ANDF@(e5b1,e5c1))
    local t2l=bsh0l+mjl
    local t2h=bsh0h+mjh+@FLR@(t2l/4294967296)
    t2l=t2l%4294967296
    t2h=t2h%4294967296
    h0=g0 e5h1=e5g1
    g0=f0 e5g1=e5f1
    f0=e0 e5f1=e5e1
    e0=d0+t1l
    e5e1=e5d1+t1h+@FLR@(e0/4294967296)
    e0=e0%4294967296
    e5e1=e5e1%4294967296
    d0=c0 e5d1=e5c1
    c0=b0 e5c1=e5b1
    b0=al e5b1=ah
    a0=t1l+t2l
    e5a1=t1h+t2h+@FLR@(a0/4294967296)
    a0=a0%4294967296
    e5a1=e5a1%4294967296
    if DBG and blk<=1 then E5DR[blk*80+t]={e5a1,a0,e5b1,b0,e5c1,c0,e5d1,d0,e5e1,e0,e5f1,f0,e5g1,g0,e5h1,h0} end
   end
   if DBG then
    if blk==0 then
     for t=0,79 do E5DW[blk*80+t]=wh[t] E5DWL[blk*80+t]=wl[t] end
     E5DA[0]=a0 E5DAH[0]=e5a1
    end
   end
   local sl2=s5va+a0
   local sh2=s5vah+e5a1+@FLR@(sl2/4294967296)
   a0=sl2%4294967296 e5a1=sh2%4294967296
   sl2=s5vb+b0
   sh2=s5vbh+e5b1+@FLR@(sl2/4294967296)
   b0=sl2%4294967296 e5b1=sh2%4294967296
   sl2=s5vc+c0
   sh2=s5vch+e5c1+@FLR@(sl2/4294967296)
   c0=sl2%4294967296 e5c1=sh2%4294967296
   sl2=s5vd+d0
   sh2=s5vdh+e5d1+@FLR@(sl2/4294967296)
   d0=sl2%4294967296 e5d1=sh2%4294967296
   sl2=s5ve+e0
   sh2=s5veh+e5e1+@FLR@(sl2/4294967296)
   e0=sl2%4294967296 e5e1=sh2%4294967296
   sl2=s5vf+f0
   sh2=s5vfh+e5f1+@FLR@(sl2/4294967296)
   f0=sl2%4294967296 e5f1=sh2%4294967296
   sl2=s5vg+g0
   sh2=s5vgh+e5g1+@FLR@(sl2/4294967296)
   g0=sl2%4294967296 e5g1=sh2%4294967296
   sl2=s5vh+h0
   sh2=s5vhh+e5h1+@FLR@(sl2/4294967296)
   h0=sl2%4294967296 e5h1=sh2%4294967296
   if DBG then E5DB[blk]={e5a1,a0,e5b1,b0,e5c1,c0,e5d1,d0,e5e1,e0,e5f1,f0,e5g1,g0,e5h1,h0} end
  end
  return @CHR@(@FLR@(e5a1/16777216)%256,@FLR@(e5a1/65536)%256,@FLR@(e5a1/256)%256,e5a1%256,
              @FLR@(a0/16777216)%256,@FLR@(a0/65536)%256,@FLR@(a0/256)%256,a0%256,
              @FLR@(e5b1/16777216)%256,@FLR@(e5b1/65536)%256,@FLR@(e5b1/256)%256,e5b1%256,
              @FLR@(b0/16777216)%256,@FLR@(b0/65536)%256,@FLR@(b0/256)%256,b0%256,
              @FLR@(e5c1/16777216)%256,@FLR@(e5c1/65536)%256,@FLR@(e5c1/256)%256,e5c1%256,
              @FLR@(c0/16777216)%256,@FLR@(c0/65536)%256,@FLR@(c0/256)%256,c0%256,
              @FLR@(e5d1/16777216)%256,@FLR@(e5d1/65536)%256,@FLR@(e5d1/256)%256,e5d1%256,
              @FLR@(d0/16777216)%256,@FLR@(d0/65536)%256,@FLR@(d0/256)%256,d0%256,
              @FLR@(e5e1/16777216)%256,@FLR@(e5e1/65536)%256,@FLR@(e5e1/256)%256,e5e1%256,
              @FLR@(e0/16777216)%256,@FLR@(e0/65536)%256,@FLR@(e0/256)%256,e0%256,
              @FLR@(e5f1/16777216)%256,@FLR@(e5f1/65536)%256,@FLR@(e5f1/256)%256,e5f1%256,
              @FLR@(f0/16777216)%256,@FLR@(f0/65536)%256,@FLR@(f0/256)%256,f0%256,
              @FLR@(e5g1/16777216)%256,@FLR@(e5g1/65536)%256,@FLR@(e5g1/256)%256,e5g1%256,
              @FLR@(g0/16777216)%256,@FLR@(g0/65536)%256,@FLR@(g0/256)%256,g0%256,
              @FLR@(e5h1/16777216)%256,@FLR@(e5h1/65536)%256,@FLR@(e5h1/256)%256,e5h1%256,
              @FLR@(h0/16777216)%256,@FLR@(h0/65536)%256,@FLR@(h0/256)%256,h0%256)
 end
 @E5V@=function(msg,sig,pk)
  if #sig~=64 or #pk~=32 then return false end
  local s={0,0,0,0,0,0,0,0,0,0,0}
  for i=0,29 do
   local q=@FLR@(i/3)+1
   s[q]=s[q]+@BYT@(sig,33+i)*2^(8*(i%3))
  end
  s[11]=@BYT@(sig,63)+@BYT@(sig,64)*256
  if not e5ltl(s,e5L) then return false end
  local R=e5dec(@SUB@(sig,1,32))
  if not R then return false end
  local A=e5dec(pk)
  if not A then return false end
  local k=e5modL(@S512@(@SUB@(sig,1,32)..pk..msg))
  local P1=e5muls(e5B,s)
  local P2=e5addp(R,e5muls(A,k))
  return e5cmp(P1)==e5cmp(P2)
 end

end
local s5me="\247\246\245\244"
-- ====== EXF-02 pure-Lua crypto END ======
local function @LM@(k)
 local a=((k%32768)*@KM4@+((@FLR@(k/32768)*@KM4@)%2147483647)*32768)%2147483647
 a=@KX@(a,@FLR@(a/128))
 a=(a+@KSD@)%2147483647
 if a<1 then a=a+2147483646 end
 return a
end
local function @KX2@(x,y) return @BX@(@FLR@(x/256),@FLR@(y/256))*256+@BX@(x%256,y%256) end
local function @MX@(k,i)
 local im=@KMA@%4294967296
 local a=(k%4294967296+(@FLR@(i/65536)*im)%4294967296*65536+(i%65536)*im)%4294967296
 a=a-(a%256)+@BX@(a%256,@FLR@(a/16777216))
 a=@KX@(a,@FLR@(a/8192))
 a=(a+@KMB@)%2147483647
 if a<1 then a=a+2147483646 end
 return a
end
local @K@=@KDEF@
local @ALN@="" local @APL@={@POOL@}
local @AST@=@MX@(@K@[3],404)
for t1=92,1,-1 do @AST@=@LM@(@AST@) local aj=@AST@%(t1+1) @APL@[t1+1],@APL@[aj+1]=@APL@[aj+1],@APL@[t1+1] end
for t1=1,93 do @ALN@=@ALN@..@APL@[t1] end
local @RB@={}
for t1=1,#@ALN@ do @RB@[@BYT@(@ALN@,t1)]=t1-1 end
local function @D8@(s)
 local n=#s local t={} local o=1 local i=1
 for q7=1,n do if not @RB@[@BYT@(s,q7)] then @WP@() end end
 while i+4<=n do
  local v=@RB@[@BYT@(s,i)]+@RB@[@BYT@(s,i+1)]*93+@RB@[@BYT@(s,i+2)]*8649+@RB@[@BYT@(s,i+3)]*804357+@RB@[@BYT@(s,i+4)]*74805201
  i=i+5
  t[o]=@CHR@(v%256) t[o+1]=@CHR@(@FLR@(v/256)%256) t[o+2]=@CHR@(@FLR@(v/65536)%256) t[o+3]=@CHR@(@FLR@(v/16777216)%256)
  o=o+4
 end
 local m=n-i+1
 if m>1 then
  local kb=m-1
  local v=@RB@[@BYT@(s,i)]
  if kb>0 then v=v+@RB@[@BYT@(s,i+1)]*93 end
  if kb>1 then v=v+@RB@[@BYT@(s,i+2)]*8649 end
  if kb>2 then v=v+@RB@[@BYT@(s,i+3)]*804357 end
  t[o]=@CHR@(v%256)
  if kb>1 then t[o+1]=@CHR@(@FLR@(v/256)%256) end
  if kb>2 then t[o+2]=@CHR@(@FLR@(v/65536)%256) end
  o=o+kb
 end
 return @CAT@(t)
end
local @B@=@D8@("@B85@")
if not @B@ then @WP@() end
@SIGCHK@
local @FD2@=0
for t1=1,#@B@,7 do @FD2@=(@FD2@*@SFM@+@KX@(@BYT@(@B@,t1)*(t1%89+3)+t1,@FLR@(@FD2@/65536)))%4294967296 end
@FD2@=@KX@(@FD2@,@FLR@(@FD2@/2048))
@FD2@=(@FD2@*@CMM2@+@IVM2@)%4294967296
@K@[2]=@MX@(@K@[2],@FD2@)
local @NMD@=@D8@("@NB85@")
if not @NMD@ then @WP@() end
local @NMS@=@MX@((@K@[1]+@K@[3])%2147483647,62)
local @NMA@={}
do
 local nd2={}
 for i=1,#@NMD@ do @NMS@=@LM@(@NMS@) nd2[i]=@BX@(@BYT@(@NMD@,i),@NMS@%256) end
 local np2=1 local nc2=0
 while np2<=#nd2 do
  local l2=nd2[np2] np2=np2+1
  if np2+l2-1>#nd2 then @WP@() end
  local nm2=""
  for j2=1,l2 do nm2=nm2..@CHR@(nd2[np2]) np2=np2+1 end
  nc2=nc2+1 @NMA@[nc2]=nm2
 end
end
@SEL@=@ENV@[@NMA@[1]]
@UPK@=@ENV@[@NMA@[2]] or @TBL@[@NMA@[4]]
if type(@SEL@)~="function" or type(@UPK@)~="function" then @WP@() end
local @XP@=@ENV@["\120\112\099\097\108\108"] if type(@XP@)~="function" then @WP@() end
@PININI@
local @MHV@=@MTH@ local @SLV@=@SEL@ local @UKV@=@UPK@
local @EF@=(@K@[4]*@EFC@+@K@[5]+@EFD@)%2147483647
local function @IZ@(d)
 local md=@BYT@(d,1)
 local rl=@BYT@(d,2)*16777216+@BYT@(d,3)*65536+@BYT@(d,4)*256+@BYT@(d,5)
 if md==0 then
  if 5+rl~=#d then @WP@() end
  return @SUB@(d,6,5+rl)
 end
 local cl=@BYT@(d,6)*16777216+@BYT@(d,7)*65536+@BYT@(d,8)*256+@BYT@(d,9)
 if 9+cl~=#d then @WP@() end
 if rl>256*#d+4096 then @WP@() end
 local s=@SUB@(d,10,9+cl)
 local n=#s local t={} local o=1 local i=1
 while i<=n do
  local tkn=@BYT@(s,i) i=i+1
  local ll=@FLR@(tkn/16)
  if ll==15 then repeat if i>n then @WP@() end local e=@BYT@(s,i) i=i+1 ll=ll+e until e<255 end
  if i+ll-1>n or o-1+ll>rl then @WP@() end
  for j=1,ll do t[o]=@CHR@(@BYT@(s,i)) i=i+1 o=o+1 end
  local ml=tkn%16
  if ml>0 then
   if i+1>n then @WP@() end
   local off=@BYT@(s,i)+@BYT@(s,i+1)*256 i=i+2
   if ml==15 then repeat if i>n then @WP@() end local e=@BYT@(s,i) i=i+1 ml=ml+e until e<255 end
   local src=o-off
   if src<1 or o-1+ml+3>rl then @WP@() end
   for j=1,ml+3 do t[o]=t[src] o=o+1 src=src+1 end
  end
 end
 if i<=n then @WP@() end
 if o-1~=rl then @WP@() end
 return @CAT@(t)
end
local @SBX@ local @SIX@
local function @MKSBX@(k) local t={} local iv={} for i=0,255 do t[i]=i end local st=k for i=255,1,-1 do st=@LM@(st) local j=st%(i+1) t[i],t[j]=t[j],t[i] end local st2=@MX@(k%2147483647,555) for i=255,1,-1 do st2=@LM@(st2) local j=st2%(i+1) t[i],t[j]=t[j],t[i] end for i=0,255 do iv[t[i]]=i end return t,iv end
local function @DM@(s,k) if not @SIX@ then @WP@() end local sa=k local sb=@MX@(k,707) local t={} for i=1,#s do local st if i%2==1 then sa=@LM@(sa) st=sa else sb=@LM@(sb) st=sb end t[i]=@CHR@(@BX@(@SIX@[@BYT@(s,i)],st%256)) end return @CAT@(t) end
local function @CK@(s,g)
 local h=g%4294967296
 for i=1,#s do
  h=(h+@BYT@(s,i)*(i%@CKW@+@CKA@)+i)%4294967296
  if i%16==0 then h=@KX@(h,(@FLR@(h/65536)+i)%4294967296) end
 end
 h=@KX@(h,@FLR@(h/32768))
 h=(h*@CMM@+@IVM@)%4294967296
 h=@KX@(h,@FLR@(h/8192))
 h=(h*@CMM2@+@IVM2@)%4294967296
 h=@KX@(h,@FLR@(h/65536))
 return h
end
local @A1@=@SC1@ local @A2@=@SC2@ local @A3@=@SC3@
if (@A1@*3+@A2@)%@KPR@~=@A3@ then @WP@() end
local function @BT@(src,md)
 local t={}
 local pos=1
 local n=#src
 local hs=@MX@(@BSALT@,4444)
 while pos+8<=n do
  hs=@LM@(hs) local q1=hs
  hs=@LM@(hs) local q2=hs
  hs=@LM@(hs) local q3=hs
  hs=@LM@(hs) local q4=hs
  hs=@LM@(hs) local q5=hs
  hs=@LM@(hs) local q6=hs
  hs=@LM@(hs) local q7=hs
  hs=@LM@(hs) local q8=hs
  local l=@BX@(@BYT@(src,pos),q1%256)*16777216+@BX@(@BYT@(src,pos+1),q2%256)*65536+@BX@(@BYT@(src,pos+2),q3%256)*256+@BX@(@BYT@(src,pos+3),q4%256)
  local cb=@BX@(@BYT@(src,pos+4),q5%256)*16777216+@BX@(@BYT@(src,pos+5),q6%256)*65536+@BX@(@BYT@(src,pos+6),q7%256)*256+@BX@(@BYT@(src,pos+7),q8%256)
  if l<=0 or pos+8+l>n+1 then @WP@() end
  t[#t+1]={l,cb,@SUB@(src,pos+8,pos+7+l)}
  pos=pos+8+l
 end
 if pos~=n+1 then @WP@() end
 return t
end
local @SS@=@BT@(@B@,1)
if not @SS@ or #@SS@<1 then @WP@() end
local @CKU@={}
local @NSC@=#@SS@
@CKU@[@NSC@]=@KX@(@SS@[@NSC@][2],@K@[1]%4294967296)
for @Q4@=@NSC@-1,1,-1 do @CKU@[@Q4@]=@KX@(@SS@[@Q4@][2],@CKU@[@Q4@+1]) end
local m0=@SS@[1]
if not m0 then @WP@() end
local @AGGV@=0
for i=1,#@SS@ do @AGGV@=(@AGGV@*@CMM@+@CK@(@SS@[i][3],(@K@[1]+i*@KMC@)%4294967296)+i)%4294967296 end
if @AGGV@~=@AGG@ then @WP@() end
local @EV@=@ENV@ local @SV@=@STR@ local @SB@=@BYT@ local @TT@=@TBL@ local @TC@=@CAT@ local @FRV@=@FLR@ local @SUV@=@SUB@
@KVM@
local @FM@={} local @OP@={} local @DC@={} local @JS@={} local @SN@={} local @VAR@={} local @SMP@={}
local @TB@=@D8@("@TB85@")
if not @TB@ then @WP@() end
local @TBS@=@MX@((@K@[1]+@K@[3])%2147483647,60)
do
 local tb2={}
 for i=1,#@TB@ do @TBS@=@LM@(@TBS@) tb2[i]=@BX@(@BYT@(@TB@,i),@TBS@%256) end
 local rp=1
 local function rd2(cc2) local v2=0 for z2=1,cc2 do if rp>#tb2 then @WP@() end v2=v2*256+tb2[rp] rp=rp+1 end return v2 end
 local cnt2=rd2(2)
 for z2=1,cnt2 do
  local oid=rd2(2)
  if rp>#tb2 then @WP@() end
  local lay2=tb2[rp] rp=rp+1
  if rp+4>#tb2 then @WP@() end
  @FM@[oid]=lay2
  local sl2={} for q2=1,5 do sl2[q2]=tb2[rp] rp=rp+1 end
  @SMP@[oid]=sl2
 end
 cnt2=rd2(2) for z2=1,cnt2 do @JS@[rd2(2)]=1 end
 cnt2=rd2(2) for z2=1,cnt2 do @DC@[z2]=rd2(2) end
 cnt2=rd2(2) for z2=1,cnt2 do @SN@[z2]=rd2(2) end
 cnt2=rd2(2) for z2=1,cnt2 do @OP@[z2]=rd2(2) end
end
local @D@
local @IV@=0
for t1=1,#@OP@ do @IVUP@ end
if @IV@~=@IVV@ then @WP@() end
local @MWLN@={[0]=4,3,2,4,5,4,3,4,5,6,3,3,7,8,7,6,6}
local @DS@ local @IST@={nc=0,sc={},pr={}}
local @CL@ local @KS@ local @GS@ local @GNV@ local @SNV@ local @PL@ local @MC@ local @RT@ local @RN@ local @TRP@ local @RNA@ local @RNB@ local @RNC@
local @CRA@ local @JR@
local @MK@={}
local @PK@=function(...) return {n=@SEL@('#',...),...} end
function @CL@(fr,tp)
 local vo=fr.vo if not vo then return end
 local r=fr.r local m=fr.m
 for rg,c in pairs(vo) do if rg>=tp then c.v=r[m[rg]] c.r=nil c.m=nil vo[rg]=nil end end
end
function @KS@(P,i) local v=P[@FK@][i] if v==nil then local e=P[@FKS@][i] if e then v=@GS@(e,P.st) P[@FK@][i]=v end end return v end
local function @PD@(s,a,b,k)
 local t={} local n=0
 if a<1 or b>#s then @WP@() end
 for i=a,b do
  local s0=@MX@(k,i)
  local s1=@LM@(s0) local s2=@LM@(s1)
  local q=(i-1)%5 local kb
  if q==0 then kb=s1%256 elseif q==1 then kb=@FLR@(s1/256)%256 elseif q==2 then kb=@FLR@(s1/65536)%256 elseif q==3 then kb=@FLR@(s1/16777216)%256 else kb=s2%256 end
  n=n+1 t[n]=@CHR@(@BX@(@SIX@[@BYT@(s,i)],kb))
 end
 return @CAT@(t)
end
function @GS@(gi,ist)
 local v=ist.sc[gi]
 if v~=nil then return v end
 local sc=@SS@[@PPV@]
 if not sc then @WP@() end
 if not ist.lt then
  local h2=@PD@(sc[3],1,2,@PE@)
  if #h2<2 then @WP@() end
  local cnt=@BYT@(h2,1)*256+@BYT@(h2,2)
  if cnt<1 then @WP@() end
  local hd=@PD@(sc[3],3,2*cnt+2,@PE@)
  if #hd<cnt*2 then @WP@() end
  local L={} local ac2=2*cnt+3 local fl2={}
  for t1=1,cnt do local ln=@BYT@(hd,t1*2-1)*256+@BYT@(hd,t1*2) local fg2=0 if ln>=32768 then fg2=1 ln=ln-32768 end L[t1]={ac2,ln} fl2[t1]=fg2 ac2=ac2+ln end
  ist.lt=L
  ist.ltf=fl2
 end
 local fr=ist.lt[gi]
 if not fr then @WP@() end
 local s=@PD@(sc[3],fr[1],fr[1]+fr[2]-1,@PE@)
 if not s or #s~=fr[2] then @WP@() end
 @STT@[14]=gi
 @STT2@[14]=gi
 @KVMR@(@KPK@)
 @KVMR2@(@KPK@)
 local st=@STT@[16]
 if not st or st~=@STT2@[16] then @WP@() end
 @STT@[14]=nil @STT2@[14]=nil @STT@[16]=nil @STT2@[16]=nil
 local t={}
 for t1=1,#s do st=@LM@(st) t[t1]=@CHR@(@BX@(@BYT@(s,t1),st%256)) end
 local v=@CAT@(t)
 if ist.ltf[gi]==1 then
  local fr2=ist.lt[gi+1]
  if not fr2 then @WP@() end
  local s2=@PD@(sc[3],fr2[1],fr2[1]+fr2[2]-1,@PE@)
  if not s2 or #s2~=fr2[2] then @WP@() end
  @STT@[14]=gi+1
  @STT2@[14]=gi+1
  @KVMR@(@KPK@)
  @KVMR2@(@KPK@)
  local st2=@STT@[16]
  if not st2 or st2~=@STT2@[16] then @WP@() end
  @STT@[14]=nil @STT2@[14]=nil @STT@[16]=nil @STT2@[16]=nil
  local t2={}
  for t1=1,#s2 do st2=@LM@(st2) t2[t1]=@CHR@(@BX@(@BYT@(s2,t1),st2%256)) end
  v=v..@CAT@(t2)
 end
 ist.sc[gi]=v
 return v
end
function @GNV@(nm,fr)
 local stg=fr.st
 local gm=stg.gm
 if not gm then gm={} stg.gm=gm end
 local v=gm[nm]
 if v~=nil then return v[1] end
 v=@PIN@[nm]
 gm[nm]={v}
 return v
end
function @SNV@(nm,val,fr)
 local stg=fr.st
 local gm=stg.gm
 if not gm then gm={} stg.gm=gm end
 gm[nm]={val}@GWR@
end
function @MC@(P,uv) return function(...) return @RN@(P,uv,P.st,...) end end
function @TRP@(Pq,st)
 local bq=st.nc+Pq[@FPH@]
 local tq={} local ts=@MX@((Pq[@FKE@]+bq*@KMA@)%2147483647,34)
 for v=1,@NOP@ do tq[v]=v end
 for v=@NOP@,2,-1 do ts=@LM@(ts) local tj=1+ts%v tq[v],tq[tj]=tq[tj],tq[v] end
 Pq[@FTP@]=tq
 local dmq=Pq[@FDM@] local dq=Pq[@FDQ@]
 for v2=1,@NOP@ do local vv2=@VAR@[v2] if vv2 then dmq[tq[dq[v2]]]=vv2[1+@LM@(ts+v2*@KMB@)%#vv2] else dmq[tq[dq[v2]]]=@D@[v2] end end
 Pq[@FTN@]=bq%4
 for kk7 in pairs(Pq[@FCO@]) do Pq[@FCO@][kk7]=nil end
end
function @RT@(st)
 st.nc=st.nc+1
 local c1=@SN@[(st.nc%#@SN@)+1]
 if @D@[c1]~=@DS@[c1] then @WP@() end
 local ndc=#@DC@
 if ndc>0 then
  local c2=@DC@[(st.nc%ndc)+1]
  if @D@[c2]~=@DS@[c2] then @WP@() end
 end
 if st.nc%@PFQ@==0 then
  if @CK@(@ALN@,(@K@[2]+@PS@)%2147483646+1)~=@PV@ then @WP@() end
  if not rawequal(@ENV@,@EV@) or not rawequal(@STR@,@SV@) or not rawequal(@BYT@,@SB@) then @WP@() end
  if not rawequal(@TBL@,@TT@) or not rawequal(@CAT@,@TC@) then @WP@() end
  if not rawequal(@FLR@,@FRV@) or not rawequal(@SUB@,@SUV@) then @WP@() end
  if not rawequal(@MTH@,@MHV@) or not rawequal(@SEL@,@SLV@) or not rawequal(@UPK@,@UKV@) then @WP@() end
  if @SUB@("\097\113\119\122",2,3)~="\113\119" or @FLR@(9.7)~=9 or @BYT@("\065\090",1)~=65 or @SLN@("\097\113\055")~=3 or @SRP@("\107\050",3)~="\107\050\107\050\107\050" or @SEL@("#",1,2,3)~=3 or @BYT@("\065\090",2)~=90 or @FLR@(2.5)~=2 then @WP@() end
 end
 if st.nc%4==0 then for kk2,kv2 in pairs(st.sc) do st.sc[kk2]=nil end end
end
function @CRA@(r,m,a,b)
 local t={} local w=0
 for i=a,b do w=w+1 t[w]=r[m[i]] end
 return t
end
local function @ST0@(P,pc)
 local key=P[@FKE@]
 local s0=@MX@(key,pc)
 local sa=@LM@(s0) local sb=@LM@(sa)
 local zc3=@LM@(sb)
 local w1=sa%256
 return w1,zc3%251
end
function @JR@(fr,pc,op)
 local i=pc-1
 local jc=fr.jc if not jc then jc={} fr.jc=jc end
 local s=jc[i]
 if s then return s end
 local P=fr.P
 local v=P[@FJT@][i]
 if not v then @WP@() end
 local key=P[@FKE@]
 local m1=@MX@(key,(i*4+2)*97+op*13)%16777216
 local m2=@MX@(key,(i*4+3)*97+op*29)%16777216
 s=(v-m1-m2)%16777216
 if s>=8388608 then s=s-16777216 end
 jc[i]=s
 return s
end
local function @MV@(P,nv,st)
 local vs=P[@FVE@][1]
 local rw=P[@FRW@] local lens=P[@FLN@] local off=P[@FOF@]
 local rot=P[@FW2@]
 local rotOk=(P[@FIB@] or 0)~=1
 for pc=1,#lens do
  local o=off[pc] local ln=lens[pc]
  local ua=0 local ub=0
  if vs~=0 then
   local s1=(vs+P[@FKSD@]*@KMC@)%2147483647 if s1<1 then s1=s1+2147483646 end
   s1=(s1+pc*@KMA@)%4294967296
   s1=s1-(s1%256)+@BX@(s1%256,@FLR@(s1/16777216))
   s1=@KX@(s1,@FLR@(s1/8192))
   s1=(s1+@KMB@)%2147483647 if s1<1 then s1=s1+2147483646 end
   ua=(s1*@KM4@)%2147483647 ua=@KX@(ua,@FLR@(ua/128)) ua=(ua+@KSD@)%2147483647 if ua<1 then ua=ua+2147483646 end
   ub=(ua*@KM4@)%2147483647 ub=@KX@(ub,@FLR@(ub/128)) ub=(ub+@KSD@)%2147483647 if ub<1 then ub=ub+2147483646 end
  end
  local na=0 local nb=0
  if nv~=0 then
   local s2=(nv+P[@FKSD@]*@KMC@)%2147483647 if s2<1 then s2=s2+2147483646 end
   s2=(s2+pc*@KMA@)%4294967296
   s2=s2-(s2%256)+@BX@(s2%256,@FLR@(s2/16777216))
   s2=@KX@(s2,@FLR@(s2/8192))
   s2=(s2+@KMB@)%2147483647 if s2<1 then s2=s2+2147483646 end
   na=(s2*@KM4@)%2147483647 na=@KX@(na,@FLR@(na/128)) na=(na+@KSD@)%2147483647 if na<1 then na=na+2147483646 end
   nb=(na*@KM4@)%2147483647 nb=@KX@(nb,@FLR@(nb/128)) nb=(nb+@KSD@)%2147483647 if nb<1 then nb=nb+2147483646 end
  end
  for j=0,ln-1 do
   local ov
   if j<4 then ov=@FLR@(ua/256^j)%256 else ov=@FLR@(ub/256^(j-4))%256 end
   local nwv
   if j<4 then nwv=@FLR@(na/256^j)%256 else nwv=@FLR@(nb/256^(j-4))%256 end
   rw[o+j]=@BX@(rw[o+j],ov)
   if rot and rotOk and j==0 then
    local st0v,zov=@ST0@(P,pc)
    local pb=@BX@(rw[o],st0v)
    local x5=(pb-zov)%251
    local y5=((x5-P[@FAFB@]+502)*P[@FAFI@])%251
    local y6
    if P[@FEP@]==0 then y6=P[@FW2I@][y5] elseif P[@FEP@]==1 then y6=P[@FW3I@][P[@FW2@][y5]] else y6=P[@FW3@][y5] end
    if y6 then
     local x6=(y6*P[@FAII@]+P[@FAFB@]-502)%251
     rw[o]=@BX@((x6+zov)%251,st0v)
    end
   end
   rw[o+j]=@BX@(rw[o+j],nwv)
  end
 end
 P[@FVE@][1]=nv
 if rotOk then P[@FEP@]=(P[@FEP@]+1)%3 end
 local gs=@MX@((P[@FKE@]+st.nc*@KMC@)%2147483647,35)
 local od={}
 for pc=1,#lens do od[pc]=pc end
 for pc=#lens,2,-1 do gs=@LM@(gs) local gj=1+gs%pc od[pc],od[gj]=od[gj],od[pc] end
 local nps={} local ac2=1
 for k5=1,#lens do local pj=od[k5] nps[pj]=ac2 ac2=ac2+lens[pj] end
 local tb={}
 for pc=1,#lens do
  local o=off[pc] local q3=nps[pc] local ln=lens[pc]
  for z2=0,ln-1 do tb[q3+z2]=rw[o+z2] end
 end
 for y3=1,ac2-1 do rw[y3]=tb[y3] end
 for y3=ac2,ac2+7 do rw[y3]=0 end
 for pc=1,#lens do off[pc]=nps[pc] end
 P[@FVC@]=(P[@FVC@]+1)%@KPR@
end
local function @CM@(P,cd,st)
 local f0=P[@FCC@]
 if f0-P[@FLS@]<@VG2@ then return end
 local tg=st.nc-P[@FLC@]
 if tg<@VR2@ then return end
 if (st.nc+P[@FPH@])%@VR2@~=0 and tg<@VR3@ then return end
 local acc=0
 local lnT=P[@FLN@] local ofT=P[@FOF@] local rwT=P[@FRW@]
 local vs0=P[@FVE@][1]
 for pc2=1,#lnT do
  local o=ofT[pc2]
  local wa=0 local wb=0
  if vs0~=0 then
   local s1=(vs0+P[@FKSD@]*@KMC@)%2147483647 if s1<1 then s1=s1+2147483646 end
   s1=(s1+pc2*@KMA@)%4294967296
   s1=s1-(s1%256)+@BX@(s1%256,@FLR@(s1/16777216))
   s1=@KX@(s1,@FLR@(s1/8192))
   s1=(s1+@KMB@)%2147483647 if s1<1 then s1=s1+2147483646 end
   wa=(s1*@KM4@)%2147483647 wa=@KX@(wa,@FLR@(wa/128)) wa=(wa+@KSD@)%2147483647 if wa<1 then wa=wa+2147483646 end
   wb=(wa*@KM4@)%2147483647 wb=@KX@(wb,@FLR@(wb/128)) wb=(wb+@KSD@)%2147483647 if wb<1 then wb=wb+2147483646 end
  end
  for j2=1,lnT[pc2] do
   local mj
   if j2<5 then mj=@FLR@(wa/256^(j2-1))%256 else mj=@FLR@(wb/256^(j2-5))%256 end
   acc=(acc*@CMM@+@BX@(rwT[o+j2-1],mj))%4294967296
  end
 end
 if (@KX@(acc,@FLR@(acc/2048))*@CMM2@+@IVM2@)%4294967296~=P[@FCK@] then @WP@() end
 @STT@[12]=(st.nc+P[@FKE@])%2147483647
 @STT2@[12]=@STT@[12]
 @KVMR@(@KPS@)
 @KVMR2@(@KPS@)
 local tv=@STT@[11]
 if not tv or tv~=@STT2@[11] then @WP@() end
 @STT@[12]=nil @STT2@[12]=nil @STT@[11]=nil @STT2@[11]=nil
 local nv=(P[@FKE@]+P[@FVC@]*@KMA@+tv)%2147483647
 if nv<1 then nv=nv+2147483646 end
 @MV@(P,nv,st)
 P[@FLS@]=f0
 P[@FLC@]=st.nc
 local acc2=0
 local vs2=P[@FVE@][1]
 local lnT2=P[@FLN@] local ofT2=P[@FOF@] local rwT2=P[@FRW@]
 for pc2=1,#lnT2 do
  local o2=ofT2[pc2] local ln2=lnT2[pc2]
  local wa2=0 local wb2=0
  if vs2~=0 then
   local s12=(vs2+P[@FKSD@]*@KMC@)%2147483647 if s12<1 then s12=s12+2147483646 end
   s12=(s12+pc2*@KMA@)%4294967296
   s12=s12-(s12%256)+@BX@(s12%256,@FLR@(s12/16777216))
   s12=@KX@(s12,@FLR@(s12/8192))
   s12=(s12+@KMB@)%2147483647 if s12<1 then s12=s12+2147483646 end
   wa2=(s12*@KM4@)%2147483647 wa2=@KX@(wa2,@FLR@(wa2/128)) wa2=(wa2+@KSD@)%2147483647 if wa2<1 then wa2=wa2+2147483646 end
   wb2=(wa2*@KM4@)%2147483647 wb2=@KX@(wb2,@FLR@(wb2/128)) wb2=(wb2+@KSD@)%2147483647 if wb2<1 then wb2=wb2+2147483646 end
  end
  for j2=1,ln2 do
   local mj2
   if j2<5 then mj2=@FLR@(wa2/256^(j2-1))%256 else mj2=@FLR@(wb2/256^(j2-5))%256 end
   acc2=(acc2*@CMM@+@BX@(rwT2[o2+j2-1],mj2))%4294967296
  end
 end
 P[@FCK@]=(@KX@(acc2,@FLR@(acc2/2048))*@CMM2@+@IVM2@)%4294967296
 for kk4,kv4 in pairs(P[@FK@]) do if type(kv4)=="string" then P[@FK@][kk4]=nil end end
 for kk in pairs(cd) do cd[kk]=nil end
end
@JK2@
@HANDLERS@
function @PL@(id,st)
 local P=st.pr[id]
 if P then return P end
 local ord=@VD2@[id] or 0
 if ord<2 then @WP@() end
 local sc=@SS@[ord]
 if not sc then @WP@() end
 if @CK@(sc[3],(@K@[1]+ord*@KMC@)%4294967296)~=@CKU@[ord] then @WP@() end
 local key=(@K@[3]+(id-1)*@KMA@)%2147483647
 if key<1 then key=key+2147483646 end
 local pv=@AN@
 if ord>2 then local pq=@SS@[ord-1] if pq then pv=@CKU@[ord-1] end end
 key=(key+(@VD@[id] or 0)+pv)%2147483647
 if key<1 then key=key+2147483646 end

 local wq={} for v=1,@NOP@ do wq[v]=v end
 local ws=key
 for v=@NOP@,2,-1 do ws=@LM@(ws) local wj=1+ws%v wq[v],wq[wj]=wq[wj],wq[v] end
 local lw={}
 local ls=key%2147483647 if ls<1 then ls=ls+2147483646 end
 for v=1,@NOP@ do
  ls=@LM@(ls)
  local g=@FM@[v] local q=g  if g==0 or g==5 then if ls%2~=0 then q=5 else q=0 end
  elseif g==1 or g==6 then if ls%2~=0 then q=6 else q=1 end
  elseif g==3 or g==7 then if ls%2~=0 then q=7 else q=3 end end
  lw[v]=q
 end
 local wv={} local wf={}
 for v=1,@NOP@ do wv[wq[v]]=v wf[wq[v]]=lw[v] end
 local tp={}
 local ts=@MX@((key+st.nc*@KMA@)%2147483647,34)
 for v=1,@NOP@ do tp[v]=v end
 for v=@NOP@,2,-1 do ts=@LM@(ts) local tj=1+ts%v tp[v],tp[tj]=tp[tj],tp[v] end
 local dm={}
 for v=1,@NOP@ do local vv=@VAR@[v] if vv then dm[tp[wq[v]]]=vv[1+@LM@(key+v*@KMC@+st.nc*@KMB@)%#vv] else dm[tp[wq[v]]]=@D@[v] end end
 local d=@IZ@(@DM@(sc[3],key))
 if not d then @WP@() end
 local cur=1
@RDRS@
 local hq={1,2,3,4,5,6,7,8,9}
 local hs0=(key*@KSD@+@KSC@)%2147483647
 if hs0<1 then hs0=hs0+2147483646 end
 for hv=9,2,-1 do hs0=@LM@(hs0) local hj0=1+hs0%hv hq[hv],hq[hj0]=hq[hj0],hq[hv] end
 local np,va,rb,nu,nr,nk,nc,ni,nf=0,0,0,0,0,0,0,0,0
 for hv=1,9 do
  local hz=hq[hv]
  if hz==1 then np=r2() elseif hz==2 then va=r1() elseif hz==3 then rb=r1()
  elseif hz==4 then nu=r2() elseif hz==5 then nr=r2() elseif hz==6 then nk=r2()
  elseif hz==7 then nc=r2() elseif hz==8 then ni=r2() else nf=r2() end
 end
 local uvs={}
 for i=1,nu do local kd=r1() local ix=@KX2@(r2(),@FLR@(@MX@(key,400+i)/65536)) uvs[i]={kd,ix} end
 local ks={}
 local kse={}
 local @CHN@=key
 local ldx=@MTH@.ldexp
 if type(ldx)~="function" then ldx=function(m,e) return m*2^e end end
 local tw0={[0]=0,1,2,3,4,5,6}
 local ts2=(key+@KSB@)%2147483647
 if ts2<1 then ts2=ts2+2147483646 end
 for tz=6,1,-1 do ts2=@LM@(ts2) local tj2=ts2%(tz+1) tw0[tz],tw0[tj2]=tw0[tj2],tw0[tz] end
 local ttg={} for tz=0,6 do ttg[tw0[tz]]=tz end
 for i=1,nk do
  local ty=ttg[r1()]
  if ty==nil then @WP@() end
  if ty==3 then
   local ln=r1()
   if cur+ln-1>#d then @WP@() end
   ks[i]=tonumber(@SUB@(d,cur,cur+ln-1))
   if not ks[i] then @WP@() end
   cur=cur+ln
   @CHN@=@LM@(@CHN@)
  elseif ty==6 then
   local ci=@MX@(@CHN@,i)
   local c2=@LM@(ci)
   local b1=@KX@(r1(),@FLR@(ci/16777216)%256)
   local b2=@KX@(r1(),@FLR@(ci/65536)%256)
   local b3=@KX@(r1(),@FLR@(ci/256)%256)
   local b4=@KX@(r1(),ci%256)
   local b5=@KX@(r1(),@FLR@(c2/16777216)%256)
   local b6=@KX@(r1(),@FLR@(c2/65536)%256)
   local b7=@KX@(r1(),@FLR@(c2/256)%256)
   local b8=@KX@(r1(),c2%256)
   local Ez=(b1%128)*16+@FLR@(b2/16)
   local Fz=(b2%16)*281474976710656+b3*1099511627776+b4*4294967296+b5*16777216+b6*65536+b7*256+b8
   if Ez==2047 then
    if Fz==0 then ks[i]=(b1>=128) and -(1/0) or (1/0) else ks[i]=(b1>=128) and -(0/0) or (0/0) end
   elseif Ez==0 then ks[i]=ldx(Fz,-1074) else ks[i]=ldx(Fz+4503599627370496,Ez-1075) end
   if b1>=128 then ks[i]=-ks[i] end
   @CHN@=@LM@(@CHN@)
  elseif ty==4 then
   local sg=r1() local mv=0 local sh=1 local vc9=0
   while true do local bb=r1() mv=mv+(bb%128)*sh if bb<128 then break end sh=sh*128 vc9=vc9+1 if vc9>7 then @WP@() end end
   if sg==1 then
    ks[i]=-mv
    @CHN@=(@CHN@+(mv%2147483647)*@KMB@)%2147483647
   else
    local ci=@MX@(@CHN@,i)
    local vu=@KX@(mv,ci)
    @CHN@=(@CHN@+(vu%2147483647)*@KMB@)%2147483647
    if vu>=2147483648 then vu=vu-4294967296 end
    ks[i]=vu
   end
   if @CHN@<1 then @CHN@=@CHN@+2147483646 end
  elseif ty==5 then
   kse[i]=r2()
   @CHN@=@LM@(@CHN@)
  elseif ty==1 then
   ks[i]=true
   @CHN@=@LM@(@CHN@)
  elseif ty==2 then
   ks[i]=false
   @CHN@=@LM@(@CHN@)
  else
   @CHN@=@LM@(@CHN@)
  end
 end
 local ksd=@CHN@
 local kids={}
 for i=1,nc do kids[i]=r2() end
 local m0={}
 local mr0=nr+32
 for v=1,mr0 do m0[v]=v end
 local ws0=key
 for v=mr0,2,-1 do ws0=@LM@(ws0) local wj=1+ws0%v m0[v],m0[wj]=m0[wj],m0[v] end
 local km=@MX@(key,1008)%65536
 local asq=(key+@KSC@)%2147483647
 local afa=@LM@(asq)%247+3
 local afb=@LM@(asq+@KSD@)%251
 local afi=1 local abq=afa%251 local aeq=249
 while aeq>0 do if aeq%2==1 then afi=afi*abq%251 end abq=abq*abq%251 aeq=@FLR@(aeq/2) end
 local afi_inv=1 local abq2=afi local aeq2=249
 while aeq2>0 do if aeq2%2==1 then afi_inv=afi_inv*abq2%251 end abq2=abq2*abq2%251 aeq2=@FLR@(aeq2/2) end
 local key2=0
 local wv2
 if @BL@==1 then
  key2=(key+@K@[1]*@KSB@+@KSC@)%2147483647
  if key2<1 then key2=key2+2147483646 end
  local wq2={} for v=1,@NOP@ do wq2[v]=v end
  local ws2=key2
  for v=@NOP@,2,-1 do ws2=@LM@(ws2) local wj=1+ws2%v wq2[v],wq2[wj]=wq2[wj],wq2[v] end
  wv2={}
  for v=1,@NOP@ do wv2[wq2[v]]=v end
 end
 local wv2i
 if wv2 then wv2i={} for qa2,qb2 in pairs(wv2) do wv2i[qb2]=qa2 end end
 local wv3
 if @BL@==1 then
  local key3=(key+@KSB@*@KMA@+@KSC@+@KSD@)%2147483647
  if key3<1 then key3=key3+2147483646 end
  local wq3={} for v=1,@NOP@ do wq3[v]=v end
  local ws3=key3
  for v=@NOP@,2,-1 do ws3=@LM@(ws3) local wj3=1+ws3%v wq3[v],wq3[wj3]=wq3[wj3],wq3[v] end
  wv3={}
  for v=1,@NOP@ do wv3[wq3[v]]=v end
 end
 local wv3i
 if wv3 then wv3i={} for qa3,qb3 in pairs(wv3) do wv3i[qb3]=qa3 end end
 local key4=@MX@(key,@IK4@)
 local wq4={} for v=1,@NOP@ do wq4[v]=v end
 local ws4=key4
 for v=@NOP@,2,-1 do ws4=@LM@(ws4) local wj4=1+ws4%v wq4[v],wq4[wj4]=wq4[wj4],wq4[v] end
 local wv4={} for v=1,@NOP@ do wv4[wq4[v]]=v end
 local key5=@MX@(key,@IK5@)
 local wq5={} for v=1,@NOP@ do wq5[v]=v end
 local ws5=key5
 for v=@NOP@,2,-1 do ws5=@LM@(ws5) local wj5=1+ws5%v wq5[v],wq5[wj5]=wq5[wj5],wq5[v] end
 local wv5={} for v=1,@NOP@ do wv5[wq5[v]]=v end
 local key6=@MX@(key,@IK6@)
 local wq6={} for v=1,@NOP@ do wq6[v]=v end
 local ws6=key6
 for v=@NOP@,2,-1 do ws6=@LM@(ws6) local wj6=1+ws6%v wq6[v],wq6[wj6]=wq6[wj6],wq6[v] end
 local wv6={} for v=1,@NOP@ do wv6[wq6[v]]=v end
 local o5=@MX@(key,@IKO@)%6
 local isaB=0
 if @ISAB@==1 then isaB=@MX@(key,@IKB@)%2 end
 local code={}
 local lens={}
 local nb2={}
 local nl2=@FLR@((ni+1)/2)
 for i=1,nl2 do nb2[i]=r1() end
 local tot=0
 for i=1,ni do
  local pk=@FLR@((i-1)/2)+1
  local lv
  if i%2==1 then lv=nb2[pk]%16 else lv=@FLR@(nb2[pk]/16)%16 end
  lens[i]=lv tot=tot+lv
 end
 local odr={}
 local ost=@MX@(key,@IKS@)
 for k=1,ni do odr[k]=k end
 for k=ni,2,-1 do ost=@LM@(ost) local j=1+ost%k odr[k],odr[j]=odr[j],odr[k] end
 local off={}
 local ac=1
 for i=1,ni do local pj=odr[i] off[pj]=ac ac=ac+lens[pj] end
 if cur+tot-1>#d then @WP@() end
 local rws=@SUB@(d,cur)
 cur=cur+tot
 local rw={}
 for i=1,tot do rw[i]=@BYT@(rws,i) end
 local v9=(key*@KMB@+@VEK@+@EF@)%2147483647
 if v9<1 then v9=v9+2147483646 end
 local @K9@=@KEP@[id] or 0
 for @A9@=1,@K9@ do
  local @LA9@=3+@LM@(@MX@(key,@IKV1@+@A9@))%246
  local @LB9@=2+@LM@(@MX@(key,@IKV2@+@A9@))%2147483644
  v9=(v9*@LA9@+@LB9@)%2147483647
  if v9<1 then v9=v9+2147483646 end
 end
 local ckv=0
 for pc=1,ni do
  local o=off[pc] local ln=lens[pc]
  local s1=(v9+ksd*@KMC@)%2147483647 if s1<1 then s1=s1+2147483646 end
  s1=(s1+pc*@KMA@)%4294967296
  s1=s1-(s1%256)+@BX@(s1%256,@FLR@(s1/16777216))
  s1=@KX@(s1,@FLR@(s1/8192))
  s1=(s1+@KMB@)%2147483647 if s1<1 then s1=s1+2147483646 end
  local wa=(s1*@KM4@)%2147483647 wa=@KX@(wa,@FLR@(wa/128)) wa=(wa+@KSD@)%2147483647 if wa<1 then wa=wa+2147483646 end
  local wb=(wa*@KM4@)%2147483647 wb=@KX@(wb,@FLR@(wb/128)) wb=(wb+@KSD@)%2147483647 if wb<1 then wb=wb+2147483646 end
  for j5=1,ln do
   local mj
   if j5<5 then mj=@FLR@(wa/256^(j5-1))%256 else mj=@FLR@(wb/256^(j5-5))%256 end
   ckv=(ckv*@CMM@+@BX@(rw[o+j5-1],mj))%4294967296
  end
 end
 ckv=@KX@(ckv,@FLR@(ckv/2048))
 ckv=(ckv*@CMM2@+@IVM2@)%4294967296
 if ckv~=@CK3@[id] then @WP@() end
 local @VE@={v9}
 local jt={}
 local nj=r2()
 for z=1,nj do
  local ji=r2()
  local jv=r1()*65536+r1()*256+r1()
  local t0=@MX@(key,ji*4+3)
  local c1=@LM@(t0) local c2=@LM@(c1) local c3=@LM@(c2)
  local h1=@FLR@(jv/65536) local h2=@FLR@(jv/256)%256 local h3=jv%256
  h1=@BX@(h1,c3%256) h2=@BX@(h2,@FLR@(c3/256)%256) h3=@BX@(h3,@FLR@(c3/65536)%256)
  jv=h1*65536+h2*256+h3
  jt[ji]=jv
 end
 local fl={}
 for i=1,nf do local stt=r4() local pp=r4() fl[stt]=pp end
 if cur~=#d+1 then @WP@() end
 local vt={}
 local pft={} local stt={}
 local ld=function(pc)
  local lb={}
  local o=off[pc]
  if not o then @WP@() end
  local ln=lens[pc]
  local pw=pft[pc]
  local st=stt[pc]
  if not pw then
   local s0=@MX@(key,pc)
   local sa=@LM@(s0) local sb=@LM@(sa)
   local zc3=@LM@(sb)
   local w1=sa%256 local w2=@FLR@(sa/256)%256 local w3=@FLR@(sa/65536)%256 local w4=@FLR@(sa/16777216)%256
   local w5=sb%256 local w6=@FLR@(sb/256)%256 local w7=@FLR@(sb/65536)%256 local w8=@FLR@(sb/16777216)%256
   if @BL@==1 then
    local t0=@MX@(key2,pc)
    local c1=@LM@(t0) local c2=@LM@(c1)
    w2=@BX@(w2,c1%256) w3=@BX@(w3,@FLR@(c1/256)%256) w4=@BX@(w4,@FLR@(c1/65536)%256) w5=@BX@(w5,@FLR@(c1/16777216)%256)
    w6=@BX@(w6,c2%256) w7=@BX@(w7,@FLR@(c2/256)%256) w8=@BX@(w8,@FLR@(c2/65536)%256)
   end
   pw={1,2,3,4,5,6,7}
   local pn0=ln-1
   if isaB==1 then
    local ol6={}
    for m7=0,ln-1 do ol6[m7]=m7 end
    local ps5=@LM@(@LM@(zc3))
    for m7=ln-1,1,-1 do ps5=@LM@(ps5) local qp5=ps5%(m7+1) ol6[m7],ol6[qp5]=ol6[qp5],ol6[m7] end
    pw[0]=ol6[0]
    for m7=1,ln-1 do pw[m7]=ol6[m7] end
   elseif pn0>1 then
    local ps4=@LM@(zc3)
    for m=pn0,2,-1 do ps4=@LM@(ps4) local qp=1+ps4%m pw[m],pw[qp]=pw[qp],pw[m] end
   end
   st={[0]=w1,zo=zc3%251,w2,w3,w4,w5,w6,w7,w8}
   pft[pc]=pw
   stt[pc]=st
  end
  local v1,v2,v3,v4,v5,v6,v7,v8=0,0,0,0,0,0,0,0
  local vs=@VE@[1]
  if vs~=0 then
   local w0=(vs+ksd*@KMC@)%2147483647 if w0<1 then w0=w0+2147483646 end
   w0=(w0+pc*@KMA@)%4294967296
   w0=w0-(w0%256)+@BX@(w0%256,@FLR@(w0/16777216))
   w0=@KX@(w0,@FLR@(w0/8192))
   w0=(w0+@KMB@)%2147483647 if w0<1 then w0=w0+2147483646 end
   local wa=(w0*@KM4@)%2147483647 wa=@KX@(wa,@FLR@(wa/128)) wa=(wa+@KSD@)%2147483647 if wa<1 then wa=wa+2147483646 end
   local wb=(wa*@KM4@)%2147483647 wb=@KX@(wb,@FLR@(wb/128)) wb=(wb+@KSD@)%2147483647 if wb<1 then wb=wb+2147483646 end
   v1=wa%256 v2=@FLR@(wa/256)%256 v3=@FLR@(wa/65536)%256 v4=@FLR@(wa/16777216)%256
   v5=wb%256 v6=@FLR@(wb/256)%256 v7=@FLR@(wb/65536)%256 v8=@FLR@(wb/16777216)%256
  end
  vt[0]=v1 vt[1]=v2 vt[2]=v3 vt[3]=v4 vt[4]=v5 vt[5]=v6 vt[6]=v7 vt[7]=v8
  local pn=ln-1
  for m=1,pn do
   local s2=pw[m]
   lb[m+1]=@BX@(@BX@(rw[o+s2],vt[s2]),st[s2])
  end
  local tp2=P[@FTP@]
  local b1
  if isaB==1 then b1=@BX@(@BX@(rw[o+pw[0]],vt[pw[0]]),st[0]) else b1=@BX@(@BX@(rw[o],v1),st[0]) end
  local x5=(b1-st.zo)%251
  local y5=((x5-afb+502)*afi)%251
  local u5
  if o5==0 then u5=wv4[wv5[wv6[y5]]]
  elseif o5==1 then u5=wv4[wv6[wv5[y5]]]
  elseif o5==2 then u5=wv5[wv4[wv6[y5]]]
  elseif o5==3 then u5=wv5[wv6[wv4[y5]]]
  elseif o5==4 then u5=wv6[wv4[wv5[y5]]]
  else u5=wv6[wv5[wv4[y5]]] end
  local t
  if @BL@==1 then
   if P[@FEP@]==1 then t=wv2[u5] elseif P[@FEP@]==2 then t=wv3[u5] else t=u5 end
  else t=u5 end
  local op=wv[t]
  if not op then @WP@() end
  local kmv=@MX@(key,pc*131+op)%65536
  local L=wf[t]
  if ln<@MWLN@[L] then @WP@() end
  local b2=lb[2] local b3=lb[3] local b4=lb[4] local b5=lb[5] local b6=lb[6] local b7=lb[7] local b8=lb[8]
  local a,b2v,c2v,sv,kv=0,0,0,0,0
  if L==0 then a=b2 b2v=b3 c2v=b4
  elseif L==1 then a=b2 b2v=b3
  elseif L==2 then a=b2
  elseif L==3 then a=b2 kv=ku((isaB==1 and (b3+b4*256) or (b3*256+b4)),km)
  elseif L==4 then
   a=b2 sv=(isaB==1 and (b3+b4*256+b5*65536) or (b3*65536+b4*256+b5))
   if @JS@[op] then sv=0
   else
    local m=@MX@(key,pc*4+1)%16777216
    sv=(sv-m)%16777216
    if sv>=8388608 then sv=sv-16777216 end
   end
  elseif L==5 then b2v=b2 a=b3 c2v=b4
  elseif L==6 then b2v=b2 a=b3
  elseif L==7 then kv=ku((isaB==1 and (b2+b3*256) or (b2*256+b3)),km) a=b4
  elseif L==8 then a=b2 b2v=b3 kv=ku((isaB==1 and (b4+b5*256) or (b4*256+b5)),km)
  elseif L==9 then a=b2 kv=ku((isaB==1 and (b3+b4*256) or (b3*256+b4)),km) b2v=ku((isaB==1 and (b5+b6*256) or (b5*256+b6)),km)
  elseif L==10 then a=b2 c2v=b3
  elseif L==11 then a=b2 b2v=b3
  elseif L==12 then a=b2 b2v=b3 c2v=b4 sv=b5 kv=ku((isaB==1 and (b6+b7*256) or (b6*256+b7)),km)
  elseif L==13 then
   a=b2 b2v=ku((isaB==1 and (b3+b4*256) or (b3*256+b4)),km) c2v=b5 sv=b6 kv=ku((isaB==1 and (b7+b8*256) or (b7*256+b8)),km)
  elseif L==14 then a=b2 kv=ku((isaB==1 and (b6+b7*256) or (b6*256+b7)),km)
  elseif L==15 then
   a=b2 b2v=b3
   sv=(isaB==1 and (b4+b5*256+b6*65536) or (b4*65536+b5*256+b6))
   if not @JS@[op] then
    local m=@MX@(key,pc*4+1)%16777216
    sv=(sv-m)%16777216
    if sv>=8388608 then sv=sv-16777216 end
   end
  elseif L==16 then a=b2 kv=ku((isaB==1 and (b3+b4*256) or (b3*256+b4)),km) b2v=ku((isaB==1 and (b5+b6*256) or (b5*256+b6)),km)
  end
  if op~=@CLSID@ and (L==3 or L==7 or L==8 or L==9 or L==12 or L==13 or L==14 or L==16) then kv=@KX2@(kv,kmv) end
  local mp=@SMP@[op]
  if not mp then @WP@() end
  return {[1]=tp2[t],[mp[1]]=a,[mp[2]]=b2v,[mp[3]]=c2v,[mp[4]]=sv,[mp[5]]=kv,[7]=op,[8]=dm[tp2[t]]}
 end
 P={[@FNP@]=np,[@FVA@]=va,[@FUV@]=uvs,[@FK@]=ks,[@FKS@]=kse,[@FCO@]=code,[@FFL@]=fl,[@FKD@]=kids,[@FKE@]=key,[@FNR@]=nr,[@FRB@]=rb,[@FDM@]=dm,[@FTP@]=tp,[@FTN@]=st.nc,[@FLD@]=ld,[@FJT@]=jt,[@FM0@]=m0,[@FVE@]=@VE@,[@FVC@]=0,[@FRW@]=rw,[@FLN@]=lens,[@FOF@]=off,[@FCC@]=0,[@FLS@]=0,[@FLC@]=0,[@FCK@]=ckv,[@FKSD@]=ksd,[@FDQ@]=wq,[@FPH@]=key%@VR2@,[@FEP@]=(1+(@KEP@[id] or 0))%3,[@FAFI@]=afi,[@FAFB@]=afb,[@FAII@]=afi_inv,[@FW2@]=wv2,[@FW2I@]=wv2i,[@FW3@]=wv3,[@FW3I@]=wv3i,[@FIB@]=isaB}
 st.pr[id]=P
 P.st=st
 return P
end
@RN@=function(P,uv,st,...)
 local n4=(st.nc+P[@FPH@])%4
 if P[@FTN@]~=n4 then @TRP@(P,st) end
 local fr={}
 fr.P=P
 fr.st=st
 fr.uv=uv
 local r={}
 fr.r=r
 local MR=P[@FNR@]+32
 local fk=(P[@FKE@]*3+st.nc*11+7)%2147483646+1
 local m={}
 for ri=1,MR do m[ri]=ri end
 local ws1=fk
 for ri=MR,2,-1 do ws1=@LM@(ws1) local rj=1+ws1%ri m[ri],m[rj]=m[rj],m[ri] end
 fr.m=m
 fr.vo=false
 fr.jc=false
 local rb=P[@FRB@]
 local np=P[@FNP@]
 if P[@FVA@]==1 then
  local args=@PK@(...)
  for i=1,np do r[m[rb+i]]=args[i] end
  local nv=args.n-np
  if nv<0 then nv=0 end
  local va={n=nv}
  for i=1,nv do va[i]=args[np+i] end
  fr.va=va
 else
  local na=select('#',...)
  for i=1,np do if i<=na then r[m[rb+i]]=select(i,...) end end
 end
 local code=P[@FCO@]
 local dm=P[@FDM@]
 local pc=1
 local tk=0
 local rc=0
 local ok2,er2
 local function dspLoop()
  while true do
   local ins=code[pc]
   if not ins then ins=P[@FLD@](pc) if not ins then @WP@() end code[pc]=ins end
   pc=pc+1
   local t=ins[7]
   @HOTDISP@
   tk=tk+1
   if tk>@ROT@ then
    tk=0
    @RT@(st)
    for kk in pairs(code) do code[kk]=nil end
    fr.jc=false
    fk=@LM@(fk)
    local m2={}
    for i=1,MR do m2[i]=i end
    local ws2=fk
    for i=MR,2,-1 do ws2=@LM@(ws2) local j=1+ws2%i m2[i],m2[j]=m2[j],m2[i] end
    local rz={}
    for i=1,MR do rz[i]=r[m[i]] end
    for i=1,MR do m[i]=m2[i] end
    for i=1,MR do r[m[i]]=rz[i] end
    rc=rc+1
    if rc>=@CMK@ then rc=0 @CM@(P,code,st) end
   end
  end
 end
 ok2,er2=@XP@(function() return dspLoop() end,function(e)
  for kk in pairs(code) do code[kk]=nil end
  fr.jc=false
  fr.vo=false
  fr.halt=nil
  return e
 end)
 if not ok2 then @ERR@(er2,0) end
 @CM@(P,code,st)
 P[@FCC@]=P[@FCC@]+1
 @CL@(fr,0)
 local out=fr.halt
 if not out then @WP@() end
 if out.t then return out.f(@UPK@(out.a,1,out.n)) end
 return @UPK@(out,1,out.n)
end
@JK3@
local @IST@={nc=0,sc={},pr={}}
local e0=@PL@(1,@IST@)
return @MC@(e0,{})(...)
)TMPL";

    {
        auto rep = [&tmplT](const std::string& a, const std::string& b) {
            size_t p = 0;
            while ((p = tmplT.find(a, p)) != std::string::npos) {
                tmplT.replace(p, a.size(), b);
                p += b.size();
            }
        };
                if (rng.chance(0.6)) rep("*8649", "*93*93");
                if (rng.chance(0.6)) rep("*804357", "*93*93*93");
                if (rng.chance(0.6)) rep("*74805201", "*93*93*93*93");
                if (rng.chance(0.6)) rep("16777216", "(256*256*256)");
                if (rng.chance(0.6)) rep("65536", "(256*256)");
                if (rng.chance(0.6) && g_bc.ma > 4096) {
                    std::uint32_t hiP = g_bc.ma & 0xFFFF0000u;
                    std::uint32_t loP = g_bc.ma - hiP;
                    rep("*@KMA@", "*(" + std::to_string(hiP) + "+" + std::to_string(loP) + ")");
                }
                if (rng.chance(0.5)) rep("local b1=@BX@(@BX@(rw[o],v1),st[0])", "local b1=@BX@(st[0],@BX@(rw[o],v1))");
                if (rng.chance(0.5)) rep("(b1-st.zo)%251", "(b1+251-st.zo)%251");
                if (rng.chance(0.5)) rep("((x5-afb+502)*afi)%251", "((x5+502-afb)*afi)%251");
                if (rng.chance(0.5)) rep("t[o]=@CHR@(@BYT@(s,i))", "t[o]=@SUB@(s,i,i)");
    }

    {
        std::unordered_set<std::string> extraReserve = {
            "lay", "st", "ins", "pc", "mr", "kt", "pk", "ws", "zz", "R",
            "np", "ni", "nc", "nr", "off", "cur", "z2", "P2", "op", "d",
            "o", "pg", "q0", "b3", "s3", "n5", "wj", "\113", "t", "i", "P",
            "r", "m", "f", "c", "x", "rt", "ar", "\119", "cp", "cells", "ds",
            "c0", "qx", "qy", "qz", "rs", "t1", "t2", "t3", "t4", "j9",
            "q9", "t9", "g8", "w8", "g9"
        };
        for (const auto& e2 : extraReserve) tmplNames.insert(e2);
        size_t si = 0;
        while (si < tmplT.size()) {
            char ch = tmplT[(size_t)si];
            if (ch == '@') {
                size_t se = tmplT.find('@', si + 1);
                if (se == std::string::npos) break;
                si = se + 1;
                continue;
            }
            if ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch == '_') {
                size_t sj = si;
                while (sj < tmplT.size() &&
                       ((tmplT[(size_t)sj] >= 'a' && tmplT[(size_t)sj] <= 'z') ||
                        (tmplT[(size_t)sj] >= 'A' && tmplT[(size_t)sj] <= 'Z') ||
                        (tmplT[(size_t)sj] >= '0' && tmplT[(size_t)sj] <= '9') ||
                        tmplT[(size_t)sj] == '_')) ++sj;
                tmplNames.insert(tmplT.substr(si, sj - si));
                si = sj;
            } else {
                ++si;
            }
        }
    }
    {
        static const char* genReserve[] = {
            "a", "a8", "ag2", "b", "b16", "b3", "base", "c", "c0", "c1", "c2",
            "c3", "c4", "c5", "c6", "c7", "c8", "cells", "cp", "cur", "d", "dgz",
            "ds", "e", "f", "fl", "fr", "g", "h", "halt", "i", "idx", "ins", "is",
            "j", "j9", "jc", "jm", "k", "kids", "kse", "kt", "ku", "l", "lay",
            "m", "m0", "m6", "mb", "mc", "mg", "mr", "n", "n5", "nc", "ni", "np",
            "nr", "nu2", "nv", "o", "off", "op", "p", "pc", "pg", "pi", "pk",
            "pp", "px", "q", "q0", "q6", "q7", "q8", "qe", "qr", "qr2", "qw",
            "qx", "qy", "qy2", "qz", "qz2", "r", "r1", "r2", "r4", "rg", "rs",
            "rt", "s", "s0", "s1", "s2", "s3", "s5", "sa", "sb", "sidx", "st",
            "step", "t", "t9", "tG9", "ta7", "tb7", "tmp", "u", "uv", "v", "va",
            "vb", "vk", "vkc", "vo", "w", "w7", "w9", "wd", "wj", "ws", "x",
            "y", "z", "z1", "z2", "za", "zf", "P2", "R"
        };
        for (const char* gr : genReserve) tmplNames.insert(gr);
    }
    NameGen ng(tmplNames);
    auto N = [&]() { return ng.next(); };

    const std::string vB = N();

    const std::string vSgv = N();
    const std::string vS512 = N();
    const std::string vE5v = N();
    const std::string vX8 = N();
    const std::string vXrf = N();
    const std::string vK = N();
    const std::string vFlr = N();
    const std::string vChr = N();
    const std::string vByt = N();
    const std::string vCat = N();
    const std::string vUpk = N();
    const std::string vEnv = N();
    const std::string vMhv = N();
    const std::string vSlv = N();
    const std::string vUkv = N();
    const std::string vXt = N();
    const std::string vEf = N();
    const std::string vGt = N();
    const std::string vAt = N();
    const std::string vOt = N();
    const std::string vA8 = N();
    const std::string vO8 = N();
    const std::string vAnd = N();
    const std::string vOrr = N();
    const std::string vCku = N();
    const std::string vNsc = N();
    const std::string vQ4 = N();
    const std::string vBx = N();
    const std::string vLm = N();
    const std::string vKx = N();
    const std::string vKx2 = N();
    const std::string vChn = N();
    const std::string vCk = N();
    const std::string vPk = N();
    const std::string vMk = N();
    const std::string vEm = N();
    const std::string vFm = N();
    const std::string vOp = N();
    const std::string vDc = N();
    const std::string vDsp = N();
    const std::string vIv = N();
    const std::string vJs = N();
    const std::string vA1 = N();
    const std::string vA2 = N();
    const std::string vA3 = N();
    const std::string vPr = N();
    const std::string vSs = N();
    const std::string vCl = N();
    const std::string vKs = N();
    const std::string vGs = N();
    const std::string vSc = N();
    const std::string vPl = N();
    const std::string vMc = N();
    const std::string vRt = N();
    const std::string vRn = N();
    const std::string vRnA = N();
    const std::string vRnB = N();
    const std::string vRnC = N();
    const std::string vBt = N();
    const std::string vRb = N();
    const std::string vAl = N();
    const std::string vD8 = N();
    const std::string vIz = N();
    const std::string vDm = N();
    const std::string vVd = N();
    const std::string vPd = N();
    const std::string vPe = N();
    const std::string vDs = N();
    const std::string vEv = N();
    const std::string vSv = N();
    const std::string vWp = N();
    const std::string vNc = N();
    const std::string vSn = N();
    const std::string vSb = N();
    const std::string vTt = N();
    const std::string vTc = N();
    const std::string vV2 = N();
    const std::string vPv = N();
    const std::string vCk3 = N();
    const std::string vKep = N();
    const std::string vK9 = N();
    const std::string vA9 = N();
    const std::string vLa9 = N();
    const std::string vLb9 = N();
    const std::string vAn = N();
    const std::string vMk2 = N();
    const std::string vSbx = N();
    const std::string vSix = N();
    const std::string vAlb = N();
    const std::string vSub = N();
    const std::string vSm = N();
    const std::string vCra = N();
    const std::string vJr = N();
    const std::string vGnv = N();
    const std::string vSnv = N();
    const std::string vPin = N();
    const std::string vErr = N();
    const std::string vXp = N();
    const std::string vMv = N();
    const std::string vCm = N();
    const std::string vXe = N();
    const std::string vVar = N();
    const std::string vC31 = N();
    const std::string vC31B = N();
    const std::string vC31H = N();
    const std::string vC32 = N();
    const std::string vC24 = N();
    const std::string vC23 = N();
    const std::string vC16 = N();
    const std::string vTrp = N();
    const std::string vLt = N();
    const std::string vLtf = N();

    auto escStr = [](const std::string& s) {
        std::string o = "\"";
        char buf[8];
        for (size_t i = 0; i < s.size(); ++i) {
            std::snprintf(buf, sizeof(buf), "\\%03u", (unsigned)(unsigned char)s[i]);
            o += buf;
        }
        o += "\"";
        return o;
    };

    static const char* kwList[] = {
        "and", "break", "do", "else", "elseif", "end", "false", "for",
        "function", "if", "in", "local", "nil", "not", "or", "repeat",
        "return", "then", "true", "until", "while",
        "getfenv", "_G", "rawequal", "error", "tonumber", "select",
        "pairs", "type", "ipairs", "setmetatable", "unpack", "next",
        "tostring", "pcall", "xpcall"
    };
    std::unordered_set<std::string> kwSet(kwList, kwList + sizeof(kwList) / sizeof(kwList[0]));
    std::unordered_map<std::string, std::string> idMap;
    for (const std::string& nm : tmplNames) idMap[nm] = N();
    auto idch2 = [](char x) {
        return (x >= 'a' && x <= 'z') || (x >= 'A' && x <= 'Z') ||
               (x >= '0' && x <= '9') || x == '_';
    };
    bool noRen = std::getenv("EXF_NORENAME") != nullptr;
    auto renameIdents = [&](const std::string& s) {
        if (noRen) return s;
        std::string o;
        o.reserve(s.size() + 64);
        size_t i = 0;
        int brace = 0;
        bool renDbg = std::getenv("EXF_RENDBG") != nullptr;
        bool lastRen = false;
        while (i < s.size()) {
            char ch = s[i];
            if (ch == '@') {
                size_t se = s.find('@', i + 1);
                if (se == std::string::npos) {
                    o.push_back(ch);
                    ++i;
                    continue;
                }
                o.append(s, i, se - i + 1);
                i = se + 1;
                continue;
            }
            if (ch == '"' || ch == '\'') {
                char q = ch;
                o.push_back(ch);
                ++i;
                while (i < s.size()) {
                    if (s[i] == '\\') {
                        o.push_back(s[i]);
                        if (i + 1 < s.size()) o.push_back(s[i + 1]);
                        i += 2;
                        continue;
                    }
                    o.push_back(s[i]);
                    if (s[i] == q) {
                        ++i;
                        break;
                    }
                    ++i;
                }
                continue;
            }
            if (idch2(ch)) {
                size_t j = i;
                while (j < s.size() && idch2(s[j])) ++j;
                std::string tok = s.substr(i, j - i);
                bool skip = kwSet.count(tok) > 0;
                char pv = 0;
                for (int back = (int)o.size() - 1; back >= 0; --back) {
                    char oc = o[(size_t)back];
                    if (oc != ' ' && oc != '\t' && oc != '\n' && oc != '\r') {
                        pv = oc;
                        break;
                    }
                }
                if (!skip && pv == ':') skip = true;
                if (!skip && pv == '.' && (o.size() < 2 || o[o.size() - 2] != '.')) skip = true;
                if (!skip && brace > 0) {
                    size_t k2 = j;
                    while (k2 < s.size() && (s[k2] == ' ' || s[k2] == '\t' ||
                                             s[k2] == '\n' || s[k2] == '\r')) ++k2;
                    if ((pv == '{' || pv == ',') && k2 < s.size() &&
                        s[k2] == '=' && (k2 + 1 >= s.size() || s[k2 + 1] != '=')) {
                        skip = true;
                    }
                }
                bool wasRen = false;
                if (!skip && idMap.find(tok) != idMap.end()) {
                    o += idMap[tok];
                    wasRen = true;
                } else {
                    o += tok;
                }
                lastRen = wasRen;
                i = j;
                continue;
            }
            if (renDbg && ch == '[' && lastRen) {
                std::fprintf(stderr, "RENDBG bracket-after-rename at %zu: ok\n", i);
            }
            lastRen = false;
            if (ch == '{') ++brace;
            if (ch == '}') --brace;
            o.push_back(ch);
            ++i;
        }
        return o;
    };
    auto junkStmts = [&](int cnt) {
        std::string o;
        for (int qq = 0; qq < cnt; ++qq) {
            std::string j1 = N(), j2 = N();
            std::uint64_t c1 = 1000 + rng.range(999999);
            std::uint64_t c2 = 3 + rng.range(94);
            std::uint64_t c3 = 1000 + rng.range(999999);
            int jf = (int)rng.range(6);
            if (jf == 0)
                o += "local " + j1 + "=" + std::to_string(c1) + " local " + j2 +
                     "=(" + j1 + "*" + std::to_string(c2) + "+" + std::to_string(c3) +
                     ")%@KPR@ " + j1 + "=" + j2 + "-" + j1 + " ";
            else if (jf == 1)
                o += "local " + j1 + "=" + std::to_string(c1) + " local " + j2 +
                     "=(" + j1 + "+" + std::to_string(c2) + ")*" + std::to_string(c3) +
                     "%@KPR@ " + j1 + "=" + j2 + "%" + std::to_string(c2) + " ";
            else if (jf == 2)
                o += "do local " + j1 + "=" + std::to_string(c1) + " local " + j2 + "=" + j1 +
                     "*" + std::to_string(c2) + "%@KPR@ " + j1 + "=" + j2 + "+" +
                     std::to_string(c3) + " end ";
            else if (jf == 3)
                o += "local " + j1 + "=" + std::to_string(c1) + " local " + j2 +
                     "=(" + j1 + "-" + std::to_string(c3) + ")%@KPR@ " + j2 + "=" + j2 +
                     "*" + std::to_string(c2) + "+" + j1 + " " + j1 + "=" + j2 + "%" +
                     std::to_string(c2) + " ";
            else if (jf == 4)
                o += "local " + j1 + "," + j2 + "=" + std::to_string(c1) + "," +
                     std::to_string(c3) + " " + j1 + "=((" + j1 + "*" + std::to_string(c2) +
                     ")%@KPR@+" + j2 + ")%@KPR@ " + j2 + "=" + j1 + "-" +
                     std::to_string(c2) + " ";
            else
                o += "local " + j1 + "=" + std::to_string(c1) + " for " + j2 + "=1,2 do " + j1 +
                     "=(" + j1 + "*" + std::to_string(c2) + "+" + std::to_string(c3) +
                     ")%@KPR@ end ";
        }
        return o;
    };

    const std::string fNp = escStr(N());
    const std::string fVa = escStr(N());
    const std::string fUv = escStr(N());
    const std::string fK = escStr(N());
    const std::string fKs = escStr(N());
    const std::string fCo = escStr(N());
    const std::string fFl = escStr(N());
    const std::string fKid = escStr(N());
    const std::string fKe = escStr(N());
    const std::string fNr = escStr(N());
    const std::string fRb = escStr(N());
    const std::string fDm = escStr(N());
    const std::string fLd = escStr(N());
    const std::string fJt = escStr(N());
    const std::string fM0 = escStr(N());
    const std::string fVe = escStr(N());
    const std::string fVc = escStr(N());
    const std::string fRw = escStr(N());
    const std::string fLn = escStr(N());
    const std::string fOf = escStr(N());
    const std::string fCc = escStr(N());
    const std::string fLs = escStr(N());
    const std::string fLcx = escStr(N());
    const std::string fCk3 = escStr(N());
    const std::string fDq = escStr(N());
    const std::string fTp = escStr(N());
    const std::string fTn = escStr(N());
    const std::string fPh = escStr(N());
    const std::string fEp = escStr(N());
    const std::string fafi = escStr(N());
    const std::string fafb = escStr(N());
    const std::string faii = escStr(N());
    const std::string fW2 = escStr(N());
    const std::string fW2I = escStr(N());
    const std::string fW3 = escStr(N());
    const std::string fW3I = escStr(N());
    const std::string fW4 = escStr(N());
    const std::string fW4F = escStr(N());
    const std::string vNma = N(), vApl = N(), vAst = N(), vFd2 = N(), vNmd = N(),
        vNms = N(), vTb = N(), vTbs = N(), vAggv = N(),
        vFrv = N(), vSuv = N(), vMx = N(), vStr = N(), vMth = N(), vTbl = N();
    const std::string vSt0 = N();
    const std::string fIb = escStr(N());
    const std::string vMw = N();
    const std::string fKsd = escStr(N());
    const std::string vSln = N();
    const std::string vSrp = N();
    const std::string vSel = N();
    const std::string fCm = escStr(N());
    const std::string fCe = escStr(N());

    std::vector<std::array<int, 5>> opSlots((size_t)VOP_DECOY11 + 1);
    {
        std::vector<int> sp = {2, 3, 4, 5, 6};
        for (int x = 4; x > 0; --x) {
            int j = (int)rng.range((std::uint64_t)(x + 1));
            std::swap(sp[(size_t)x], sp[(size_t)j]);
        }
        for (int canon = 0; canon <= VOP_DECOY11; ++canon)
            for (int q = 0; q < 5; ++q)
                opSlots[(size_t)canon][(size_t)q] = sp[(size_t)q];
    }

    const bool timing2 = std::getenv("EXF_TIME") != nullptr;
    auto tick2 = [&timing2]() -> double {
        if (!timing2) return 0;
        return std::chrono::duration<double, std::milli>(
            std::chrono::steady_clock::now().time_since_epoch()).count();
    };
    double e0 = tick2();
    std::string alpha = b85Alphabet((std::uint32_t)b.buildSeed);
    std::string b85text = b85Encode(b.blob, alpha);
    double e1 = tick2();

    auto sectionFold = [](const std::string& blobx, std::uint32_t saltBase) {
        std::uint32_t dg = 0;
        size_t pos = 0;
        int ridx = 0;
        const size_t nn = blobx.size();
        while (pos + 8 <= nn) {
            std::uint32_t l = ((std::uint32_t)(std::uint8_t)blobx[pos] << 24) |
                              ((std::uint32_t)(std::uint8_t)blobx[pos + 1] << 16) |
                              ((std::uint32_t)(std::uint8_t)blobx[pos + 2] << 8) |
                              (std::uint32_t)(std::uint8_t)blobx[pos + 3];
            if (l == 0 || pos + 8 + l > nn + 1) break;
            ++ridx;
            std::uint32_t ck = checksum32(blobx.substr(pos + 8, l),
                                         saltBase + (std::uint32_t)ridx * g_bc.mc);
            dg = (std::uint32_t)(((std::uint64_t)dg * g_bc.cmM + ck + (std::uint64_t)ridx) &
                                 0xFFFFFFFFull);
            pos += 8 + l;
        }
        return dg;
    };
    const std::string& foldSrc = b.foldView.empty() ? b.blob : b.foldView;
    const std::string& kFoldSrc = b.kFoldView.empty() ? b.kblob : b.kFoldView;
    const std::string& kFoldSrcG = b.kFoldViewG.empty() ? b.ghostBlob : b.kFoldViewG;
    const std::uint32_t aggVal = sectionFold(foldSrc, b.blobSalt);
    const std::uint32_t kAggReal = sectionFold(kFoldSrc, b.blobSalt);
    const std::uint32_t kAggGhost = sectionFold(kFoldSrcG, b.blobSalt);

    std::uint32_t probeSalt = 1 + (std::uint32_t)rng.range(2147483645u);
    std::uint32_t probeVal = 0;

    std::vector<int> spotPool;
    for (int i = 0; i < VOP_DECOY0; ++i) spotPool.push_back(b.opId[i]);
    for (size_t x = spotPool.size() - 1; x > 0; --x) {
        size_t j = (size_t)rng.range(x + 1);
        std::swap(spotPool[x], spotPool[j]);
    }
    std::string spotLit = "{";
    for (int i = 0; i < 8; ++i) {
        if (i) spotLit += ",";
        spotLit += std::to_string(spotPool[(size_t)i]);
    }
    spotLit += "}";

    std::vector<int> canonicalOf(VOP_COUNT + 1, 0);
    for (int i = 0; i < VOP_COUNT; ++i) canonicalOf[b.opId[i]] = i;
    std::vector<int> opsOrder = b.opId;
    for (size_t i = opsOrder.size() - 1; i > 0; --i) {
        size_t j = (size_t)rng.range(i + 1);
        std::swap(opsOrder[i], opsOrder[j]);
    }
    std::string opsLit = "{";
    std::uint64_t iv = 0;
    const int ivv = (int)rng.range(3);
    static const std::string lv1 = "t1";
    const std::string lvName = [&]() {
        auto it = idMap.find(lv1);
        return it != idMap.end() ? it->second : lv1;
    }();
    std::string ivUp;
    const std::string slotFold = "+" + vSm + "[" + vOp + "[" + lvName + "]][1]*" + lvName +
        "*3+" + vSm + "[" + vOp + "[" + lvName + "]][2]*" + lvName +
        "*5+" + vSm + "[" + vOp + "[" + lvName + "]][3]*" + lvName +
        "*7+" + vSm + "[" + vOp + "[" + lvName + "]][4]*" + lvName +
        "*11+" + vSm + "[" + vOp + "[" + lvName + "]][5]*" + lvName + "*13";
    if (ivv == 0) {
        ivUp = vIv + "=(" + vIv + "+" + vOp + "[" + lvName + "]*" + lvName + "+" +
               vFm + "[" + vOp + "[" + lvName + "]]*" + lvName + "*" + lvName +
               slotFold + ")%4294967296";
    } else if (ivv == 1) {
        ivUp = vIv + "=(" + vIv + "+" + vFm + "[" + vOp + "[" + lvName + "]]*" +
               lvName + "+" + vOp + "[" + lvName + "]*" + lvName + "*" + lvName +
               slotFold + ")%4294967296";
    } else {
        ivUp = vIv + "=(" + vIv + "+" + std::to_string(g_bc.ivM) + "*" + vOp +
               "[" + lvName + "]*" + lvName + "+" + vFm + "[" + vOp + "[" +
               lvName + "]]*" + lvName + "*" + lvName + slotFold + ")%4294967296";
    }
    static const int slotW[5] = {3, 5, 7, 11, 13};
    for (size_t i = 0; i < opsOrder.size(); ++i) {
        if (i) opsLit += ",";
        opsLit += std::to_string(opsOrder[i]);
        int lay = b.opLayout[canonicalOf[opsOrder[i]]];
        for (int q = 0; q < 5; ++q)
            iv = (iv + (std::uint64_t)opSlots[(size_t)canonicalOf[opsOrder[i]]][(size_t)q] *
                         (std::uint64_t)(i + 1) * (std::uint64_t)slotW[q]) % 4294967296ull;
        if (ivv == 0) {
            iv = (iv + (std::uint64_t)opsOrder[i] * (i + 1) +
                  (std::uint64_t)lay * (i + 1) * (i + 1)) %
                 4294967296ull;
        } else if (ivv == 1) {
            iv = (iv + (std::uint64_t)lay * (i + 1) +
                  (std::uint64_t)opsOrder[i] * (i + 1) * (i + 1)) %
                 4294967296ull;
        } else {
            iv = (iv + (std::uint64_t)g_bc.ivM * (std::uint64_t)opsOrder[i] * (i + 1) +
                  (std::uint64_t)lay * (i + 1) * (i + 1)) %
                 4294967296ull;
        }
    }
    opsLit += "}";

    static const char* E31F[] = {"2147483520+127", "2147483392+255", "2147483264+383"};
    static const char* E31BF[] = {"2147483584+62", "2147483520+126", "2147483392+254", "2147483645+1"};
    static const char* E31HF[] = {"1073741824*2", "2^31"};
    static const char* E32F[] = {"2^32", "4294967295+1"};
    static const char* E24F[] = {"4096*4096", "8192*2048", "2^24"};
    static const char* E23F[] = {"2^23", "4194304*2", "8388607+1"};
    static const char* E16F[] = {"2^16", "256*256", "65535+1"};
    const std::string e31 = E31F[(size_t)rng.range(3)];
    const std::string e31b = E31BF[(size_t)rng.range(4)];
    const std::string e31h = E31HF[(size_t)rng.range(2)];
    const std::string e32 = E32F[(size_t)rng.range(2)];
    const std::string e24 = E24F[(size_t)rng.range(3)];
    const std::string e23 = E23F[(size_t)rng.range(3)];
    const std::string e16 = E16F[(size_t)rng.range(3)];

    std::string decLit = "{";
    for (size_t i = 0; i < b.decoyIds.size(); ++i) {
        if (i) decLit += ",";
        decLit += std::to_string(b.decoyIds[i]);
    }
    decLit += "}";

    std::uint32_t junk = 100000000 + (std::uint32_t)rng.range(800000000u);

    auto trapResidues = [&](int shape, std::uint32_t A1, std::uint32_t A2,
                            std::uint32_t A3) {
        std::vector<std::uint32_t> rs;
        rs.reserve(65536);
        std::uint32_t A2p = A2 % g_bc.pr;
        std::uint32_t A3p = A3 % g_bc.pr;
        std::uint32_t N2 = A3 % 97u + 3u;
        std::uint32_t A1p1 = A1 + 1u;
        std::uint32_t A3m = A3 % 1000003u;

        for (std::uint32_t v = 0; v < 256; ++v) {
            std::uint32_t r2v;
            if (shape == 0) r2v = (v * A1 + A2) % g_bc.pr;
            else if (shape == 1) r2v = ((v * A1 + g_bc.pr - A2p) % g_bc.pr);
            else if (shape == 2) r2v = ((v + A1) % g_bc.pr) * A2p % g_bc.pr;
            else if (shape == 3) r2v = (((v * A1 + A2) % g_bc.pr) + A3p) % g_bc.pr;
            else if (shape == 4) r2v = ((v * A1 + (v % N2) * A2 + A3p) % g_bc.pr);
            else if (shape == 5) {
                std::uint32_t t5 = (v * A1 + A2) % g_bc.pr % 65536u;
                r2v = (t5 * t5 + A2p) % g_bc.pr;
            } else if (shape == 6) r2v = ((v + A1) % g_bc.pr + (v * A2p) % g_bc.pr + A3p) % g_bc.pr;
            else if (shape == 7) r2v = (v * A1p1 + A2) % g_bc.pr;
            else if (shape == 8) {
                std::uint32_t t8 = (v * A1 + A2) % g_bc.pr;
                r2v = (t8 % 1000003u * A3m + v) % g_bc.pr;
            } else if (shape == 9) r2v = ((v * v + v * A1 + A2) % g_bc.pr);
            else if (shape == 10) {
                std::uint32_t t10 = (v + A1) % g_bc.pr;
                r2v = (t10 % 65536u * (A2 % 4099u) + A3p) % g_bc.pr;
            } else {
                std::uint32_t A2m2 = A2 % 4999u;
                std::uint32_t A1m1 = A1 % 6553u + 1u;
                r2v = (v * A2m2 + (v % N2) * A1m1 + A3p) % g_bc.pr;
            }
            rs.push_back(r2v % g_bc.pr);
        }
        return rs;
    };
    auto trapGuard = [&](const std::string& varExpr) {
        for (int tries = 0; tries < 64; ++tries) {
            int shape = (int)rng.range(12);
            std::uint32_t A1 = 1 + (std::uint32_t)rng.range(999999);
            std::uint32_t A2 = (std::uint32_t)rng.range(g_bc.pr);
            std::uint32_t A3 = (std::uint32_t)rng.range(g_bc.pr);
            std::vector<std::uint32_t> rs = trapResidues(shape, A1, A2, A3);
            std::uint32_t cand = (std::uint32_t)rng.range(g_bc.pr);
            bool hit = false;
            for (std::uint32_t r : rs) if (r == cand) { hit = true; break; }
            if (hit) continue;
            std::string g;
            if (shape == 0)
                g = "if (" + varExpr + "*" + std::to_string(A1) + "+" + std::to_string(A2) +
                    ")%@KPR@==" + std::to_string(cand) + " then " + vWp + "() end ";
            else if (shape == 1)
                g = "if (" + varExpr + "*" + std::to_string(A1) + "-" + std::to_string(A2 % g_bc.pr) +
                    "+4*@KPR@)%@KPR@==" + std::to_string(cand) + " then " + vWp + "() end ";
            else if (shape == 2)
                g = "if ((" + varExpr + "+" + std::to_string(A1) + ")%@KPR@*" + std::to_string(A2 % g_bc.pr) +
                    ")%@KPR@==" + std::to_string(cand) + " then " + vWp + "() end ";
            else if (shape == 3)
                g = "if ((" + varExpr + "*" + std::to_string(A1) + "+" + std::to_string(A2) +
                    ")%@KPR@+" + std::to_string(A3 % g_bc.pr) + ")%@KPR@==" + std::to_string(cand) +
                    " then return -1 end ";
            else if (shape == 4)
                g = "if (" + varExpr + "*" + std::to_string(A1) + "+(" + varExpr + "%" +
                    std::to_string(A3 % 97u + 3u) + ")*" + std::to_string(A2) + "+" +
                    std::to_string(A3 % g_bc.pr) + ")%@KPR@==" + std::to_string(cand) +
                    " then return -1 end ";
            else if (shape == 5)
                g = "if ((" + varExpr + "*" + std::to_string(A1) + "+" + std::to_string(A2) +
                    ")%@KPR@%65536*((" + varExpr + "*" + std::to_string(A1) + "+" + std::to_string(A2) +
                    ")%@KPR@%65536)+" + std::to_string(A2 % g_bc.pr) + ")%@KPR@==" +
                    std::to_string(cand) + " then return -1 end ";
            else if (shape == 6)
                g = "if ((" + varExpr + "+" + std::to_string(A1) + ")%@KPR@+(" + varExpr + "*" +
                    std::to_string(A2 % g_bc.pr) + ")%@KPR@+" + std::to_string(A3 % g_bc.pr) +
                    ")%@KPR@==" + std::to_string(cand) + " then " + vWp + "() end ";
            else if (shape == 7)
                g = "if (" + varExpr + "*" + std::to_string(A1 + 1) + "+" + std::to_string(A2) +
                    ")%@KPR@==" + std::to_string(cand) + " then " + vWp + "() end ";
            else if (shape == 8)
                g = "local tG9=(" + varExpr + "*" + std::to_string(A1) + "+" + std::to_string(A2) +
                    ")%@KPR@ if (tG9%1000003*" + std::to_string(A3 % 1000003u) + "+" + varExpr +
                    ")%@KPR@==" + std::to_string(cand) + " then " + vWp + "() end ";
            else
                g = "if (" + varExpr + "*" + varExpr + "+" + varExpr + "*" + std::to_string(A1) +
                    "+" + std::to_string(A2) + ")%@KPR@==" + std::to_string(cand) +
                    " then return -1 end ";
            if (shape == 10)
                g = "if ((((" + varExpr + "+" + std::to_string(A1) + ")%@KPR@)%65536*" +
                    std::to_string(A2 % 4099u) + "+" + std::to_string(A3 % g_bc.pr) + ")%@KPR@==" +
                    std::to_string(cand) + ") then return -1 end ";
            else if (shape == 11)
                g = "if ((" + varExpr + "*" + std::to_string(A2 % 4999u) + "+(" + varExpr + "%" +
                    std::to_string(A3 % 97u + 3u) + ")*" + std::to_string(A1 % 6553u + 1u) + "+" +
                    std::to_string(A3 % g_bc.pr) + ")%@KPR@==" + std::to_string(cand) +
                    ") then return -1 end ";
            return g;
        }
        return std::string("");
    };

    std::string tblB85, nmB85, kdefLit, poolLit, efcLit, efdLit;
    std::string jsLit = "{[" + std::to_string(b.opId[VOP_JMP]) + "]=1," +
                        "[" + std::to_string(b.opId[VOP_JIFF]) + "]=1," +
                        "[" + std::to_string(b.opId[VOP_JIFT]) + "]=1," +
                        "[" + std::to_string(b.opId[VOP_FORPREP]) + "]=1," +
                        "[" + std::to_string(b.opId[VOP_FORLOOP]) + "]=1," +
                        "[" + std::to_string(b.opId[VOP_FORPREP1]) + "]=1," +
                        "[" + std::to_string(b.opId[VOP_FORLOOP1]) + "]=1}";

    {
        std::string tr;
        auto pu2 = [&tr](std::uint32_t v) {
            tr.push_back((char)((v >> 8) & 0xFFu));
            tr.push_back((char)(v & 0xFFu));
        };
        pu2((std::uint32_t)VOP_COUNT);
        for (int canon = 0; canon < VOP_COUNT; ++canon) {
            pu2((std::uint32_t)b.opId[canon]);
            tr.push_back((char)(std::uint8_t)b.opLayout[canon]);
            for (int q = 0; q < 5; ++q)
                tr.push_back((char)(std::uint8_t)opSlots[(size_t)canon][(size_t)q]);
        }
        static const int jsOps[] = {VOP_JMP, VOP_JIFF, VOP_JIFT, VOP_FORPREP,
                                    VOP_FORLOOP, VOP_FORPREP1, VOP_FORLOOP1};
        pu2(7);
        for (int jo : jsOps) pu2((std::uint32_t)b.opId[jo]);
        pu2((std::uint32_t)b.decoyIds.size());
        for (int dd : b.decoyIds) pu2((std::uint32_t)dd);
        pu2((std::uint32_t)spotPool.size());
        for (int sp2 : spotPool) pu2((std::uint32_t)sp2);
        pu2((std::uint32_t)opsOrder.size());
        for (int oo : opsOrder) pu2((std::uint32_t)oo);
        std::uint32_t tblKey = mixIdx(((std::uint64_t)b.blobSalt + (std::uint64_t)b.buildSeed) % kMod31,
                                      60ull);
        tr = encryptStr(tr, tblKey);
        tblB85 = b85Encode(tr, alpha);
    }
    {
        static const char* nameList[] = {"select", "unpack", "print", "unpack"};
        std::string nr2;
        for (const char* nm2 : nameList) {
            size_t l2 = std::strlen(nm2);
            nr2.push_back((char)(std::uint8_t)l2);
            nr2 += nm2;
        }
        std::uint32_t nmKey = mixIdx(((std::uint64_t)b.blobSalt + (std::uint64_t)b.buildSeed) % kMod31,
                                     62ull);
        nr2 = encryptStr(nr2, nmKey);
        nmB85 = b85Encode(nr2, alpha);
    }
    double m3 = tick2();
    {
        std::uint32_t foldVal = strideFold(b.blob);
        std::uint32_t k2r = mixIdx(junk, foldVal);
        std::uint32_t probeSaltEff =
            (std::uint32_t)(((std::uint64_t)k2r + probeSalt) % 2147483646ull + 1ull);
        probeVal = checksum32(alpha, probeSaltEff);
    }
    {
        int kshape = (int)rng.range(3);
        auto saltStr = [&](std::uint32_t target) {
            if (kshape == 0) {
                std::uint32_t a1 = 2 + (std::uint32_t)rng.range(46340);
                std::uint64_t prod = (std::uint64_t)a1 * a1;
                std::int64_t c2 = (std::int64_t)target - (std::int64_t)prod;
                return std::to_string(a1) + "*" + std::to_string(a1) +
                       (c2 < 0 ? "-" : "+") +
                       std::to_string(c2 < 0 ? -c2 : c2);
            } else if (kshape == 1) {
                std::uint32_t b1 = 1 + (std::uint32_t)rng.range(2147483645u);
                std::uint32_t a1 = xor32(target, b1);
                return vKx + "(" + std::to_string(a1) + "," + std::to_string(b1) + ")";
            }
            std::uint32_t b1 = 3 + (std::uint32_t)rng.range(99991);
            std::int64_t c1 = 1 + (std::int64_t)rng.range(99991);
            std::int64_t a1 = (std::int64_t)target - (std::int64_t)b1 * (std::int64_t)c1;
            return "(" + std::to_string(a1) + "+" + std::to_string(b1) + "*" +
                   std::to_string(c1) + ")";
        };

        std::uint32_t k4v = 2u + 2u * (std::uint32_t)rng.range((1u << 28));
        std::uint32_t k5v = 1u + (std::uint32_t)rng.range((1u << 28));
        std::uint32_t efc = 1u + (std::uint32_t)rng.range((1u << 20) - 1u);
        const std::uint32_t M31 = 2147483647u;
        std::uint64_t tot = (((std::uint64_t)k4v % M31) * ((std::uint64_t)efc % M31) +
                             (std::uint64_t)(k5v % M31)) % M31;
        std::uint32_t efd = (std::uint32_t)(((std::uint64_t)envFoldOf() + M31 - tot) % M31);
        kdefLit = "{" + saltStr(b.blobSalt) + "," + std::to_string(junk) + "," +
                  saltStr(b.buildSeed) + "," + saltStr(k4v) + "," + saltStr(k5v) + "}";
        efcLit = std::to_string(efc);
        efdLit = std::to_string(efd);
    }
    {
        bool firstc = true;
        for (int c = 32; c <= 126; ++c) {
            if (c == 34 || c == 92) continue;
            char buf2[8];
            std::snprintf(buf2, sizeof(buf2), "\\%03u", (unsigned)c);
            if (!firstc) poolLit += ",";
            firstc = false;
            poolLit += std::string("\"") + buf2 + "\"";
        }
    }

    const std::string kSt = N(), kKvmr = N(), kKx = N(), kKsec = N(),
        kKsk = N(), kKin = N(), kPc = N(), kHh = N(), kJt = N(),
        kPr = N(), kZ = N(), kS2 = N(), kR2 = N(), kD1 = N(), kD2 = N();
    std::string kB85text = b85Encode(b.kblob, alpha);
    std::string kB85ghost = b85Encode(b.ghostBlob, alpha);

    std::string kjLit = "{[" + std::to_string(b.kOpIds[10]) + "]=1,[" +
                        std::to_string(b.kOpIds[11]) + "]=1,[" +
                        std::to_string(b.kOpIds[12]) + "]=1,[" +
                        std::to_string(b.kOpIds[13]) + "]=1,[" +
                        std::to_string(b.kOpIds[25]) + "]=1}";

    const bool kswap = (b.kSlot == 1);
    const std::string Xa = kswap ? "ins[4]" : "ins[2]";
    const std::string Xc = kswap ? "ins[2]" : "ins[4]";
    const std::string kRAr = "st.r[st.mr[" + Xa + "]]";
    const std::string kRAz = "(" + kRAr + "-st.z1[st.mr[" + Xa + "]]-st.z2[st.mr[" + Xa + "]])";
    const std::string kRAw = kRAr + "=(";
    const std::string kRAw2 = ")+st.z1[st.mr[" + Xa + "]]+st.z2[st.mr[" + Xa + "]]";
    const std::string kRBz = "(st.r[st.mr[ins[3]]]-st.z1[st.mr[ins[3]]]-st.z2[st.mr[ins[3]]])";
    const std::string kRCz = "(st.r[st.mr[" + Xc + "]]-st.z1[st.mr[" + Xc + "]]-st.z2[st.mr[" + Xc + "]])";

    struct KHDef { int opid; std::string code; };
    std::vector<KHDef> kdefs;

    auto kh = [&](int canon, const std::string& body, bool halt) {
        std::string c = "function(st,ins,pc) ";
        c += body;
        c += halt ? " return -1 end" : " return pc end";
        kdefs.push_back({b.kOpIds[(size_t)canon], c});
    };
    kh(0, kRAw + "ins[3]" + kRAw2, false);
    kh(1, kRAw + "st.kt[ins[3]]" + kRAw2, false);
    kh(2, kRAw + vK + "[ins[3]]" + kRAw2, false);
    kh(3, kRAw + kRBz + kRAw2, false);
    kh(4, kRAw + kRAz + "+" + kRBz + kRAw2, false);
    kh(5, kRAw + kRAz + "-" + kRBz + kRAw2, false);
    kh(6, kRAw + kRAz + "*" + kRBz + kRAw2, false);
    kh(7, kRAw + kRAz + "%st.kt[ins[3]]" + kRAw2, false);
    kh(8, kRAw + kRAz + "+st.kt[ins[3]]" + kRAw2, false);
    kh(9, kRAw + kRAz + "*st.kt[ins[3]]" + kRAw2, false);
    kh(10, "pc=pc+ins[3]", false);
    kh(11, "if " + kRAz + "<" + kRCz + " then pc=pc+ins[3] end", false);
    kh(12, "if " + kRAz + ">=" + kRCz + " then pc=pc+ins[3] end", false);
    kh(13, "if " + kRAz + "==" + kRCz + " then pc=pc+ins[3] end", false);
    kh(14, "st.st[ins[3]]=" + kRAz, false);
    kh(15, "local pg=st.mr[" + Xa + "] st.r[pg]=st.st[ins[3]]+st.z1[pg]+st.z2[pg]", false);
    kh(16, "local b3=ins[3] local s3=b3%256 local n5=(b3-s3)/256 local q0=0 while q0<n5 do local pg=st.mr[" + Xa + "+q0] st.st[s3+q0]=st.r[pg]-st.z1[pg]-st.z2[pg] q0=q0+1 end", true);
    kh(17, "", true);
    kh(18, kRAw + kRBz + kRAw2, false);
    kh(19, "if " + kRAr + "==nil then " + kRAw + "st.kt[ins[3]]" + kRAw2 + " end", false);
    kh(20, kRAw + vKx + "(" + kRAz + "," + kRBz + ")" + kRAw2, false);
    kh(21, kRAw + vOrr + "(" + kRAz + "," + kRBz + ")" + kRAw2, false);
    kh(22, kRAw + vAnd + "(" + kRAz + "," + kRBz + ")" + kRAw2, false);
    kh(23, kRAw + "(" + kRAz + "*2^(" + kRBz + "%12))%2147483647" + kRAw2, false);
    kh(24, kRAw + vFlr + "((" + kRAz + ")/2^(" + kRBz + "%12))" + kRAw2, false);
    kh(25, "if " + kRAz + "~=" + kRCz + " then pc=pc+ins[3] end", false);
    kh(26, kRAw + "(2147483646-(" + kRAz + "))" + kRAw2, false);
    kh(27, "local ta7=" + kRBz + " local tb7=" + kRAz + " " + kRAw + "ta7" + kRAw2 +
           " st.r[st.mr[ins[3]]]=tb7+st.z1[st.mr[ins[3]]]+st.z2[st.mr[ins[3]]]", false);
    kh(28, kRAw + "((" + kRAz + ")+st.kt[ins[3]]+st.kt[" + Xc + "])%2147483647" + kRAw2, false);
    kh(29, "st.st[ins[3]]=" + kRAz + " st.st[" + Xc + "]=" + kRAz, false);

    for (size_t x = kdefs.size() - 1; x > 0; --x) {
        size_t j = (size_t)rng.range(x + 1);
        std::swap(kdefs[x], kdefs[j]);
    }
    int kgc = 2 + (int)rng.range(2);
    std::vector<std::vector<KHDef>> kgroups((size_t)kgc);
    for (const KHDef& h : kdefs) kgroups[(size_t)rng.range(kgc)].push_back(h);
    std::vector<int> kgOrd((size_t)kgc);
    for (int g = 0; g < kgc; ++g) kgOrd[(size_t)g] = g;
    for (int g = kgc - 1; g > 0; --g) {
        int j = (int)rng.range((std::uint64_t)(g + 1));
        std::swap(kgOrd[(size_t)g], kgOrd[(size_t)j]);
    }
    std::vector<std::string> kgNames;
    for (int g = 0; g < kgc; ++g) kgNames.push_back(N());
    const std::string kq1 = N(), kq2 = N();

    std::string rdrs;
    {
        std::string rc = idMap["cur"];
        std::string dn = idMap["d"];
        std::string r1n = N(), r2n = N(), r4n = N(), kun = N();
        std::string w1 = N(), w2 = N(), w3 = N(), w4 = N();
        std::string mn = N(), kxn = N();
        std::vector<std::string> rd = {
            "local function " + r1n + "() if " + rc + ">#" + dn + " then " + vWp + "() end local " + w1 + "=" + vByt + "(" + dn + "," + rc + ") " + rc + "=" + rc + "+1 return " + w1 + " end",
            "local function " + r2n + "() if " + rc + "+1>#" + dn + " then " + vWp + "() end local " + w2 + "=" + vByt + "(" + dn + "," + rc + ")*256+" + vByt + "(" + dn + "," + rc + "+1) " + rc + "=" + rc + "+2 return " + w2 + " end",
            "local function " + r4n + "() if " + rc + "+3>#" + dn + " then " + vWp + "() end local " + w3 + "=" + vByt + "(" + dn + "," + rc + ")*16777216+" + vByt + "(" + dn + "," + rc + "+1)*65536+" + vByt + "(" + dn + "," + rc + "+2)*256+" + vByt + "(" + dn + "," + rc + "+3) " + rc + "=" + rc + "+4 return " + w3 + " end",
            "local function " + kun + "(" + mn + "," + kxn + ") return " + vBx + "(" + mn + "%256," + kxn + "%256)+256*" + vBx + "(" + vFlr + "(" + mn + "/256)," + vFlr + "(" + kxn + "/256)) end",
        };
        for (size_t x = rd.size() - 1; x > 0; --x) {
            size_t j = (size_t)rng.range(x + 1);
            std::swap(rd[x], rd[j]);
        }
        for (const std::string& rline : rd) rdrs += rline + "\n";
        idMap["r1"] = r1n;
        idMap["r2"] = r2n;
        idMap["r4"] = r4n;
        idMap["ku"] = kun;
    }

    std::string kvm = "local function " + kKx + "(s,k) local sa=k local sb=" + vMx + "(k,707) local t={} for i=1,#s do local st if i%2==1 then sa=" +
           vLm + "(sa) st=sa else sb=" + vLm + "(sb) st=sb end t[i]=" + vChr +
           "(" + vBx + "(" + vByt + "(s,i),st%256)) end return " + vCat + "(t) end\n";
    kvm += "local " + kHh + "={}\n";
    for (int g : kgOrd) {
        std::string blk = "local " + kgNames[(size_t)g] + "={";
        bool first = true;
        for (const KHDef& h : kgroups[(size_t)g]) {
            if (!first) blk += ",";
            first = false;
            blk += "[" + std::to_string(h.opid) + "]=" + h.code;
        }
        blk += "}\n";
        kvm += blk;
    }
    for (int g : kgOrd)
        kvm += "for " + kq1 + "," + kq2 + " in pairs(" + kgNames[(size_t)g] +
               ") do " + kHh + "[" + kq1 + "]=" + kq2 + " end " + kgNames[(size_t)g] + "=nil \n";
    kvm += "local " + kJt + "=" + kjLit + "\n";
    kvm += "local function " + kZ + "(z,sidx,lay,wd,ag2)\n";
    kvm += " local " + kSt + "={}\n";
    kvm += " if not z then return nil end\n";
    kvm += " local " + kKsec + "=" + vBt + "(z,2)\n";
    kvm += " if not " + kKsec + " or not " + kKsec + "[sidx] then return nil end\n";
    kvm += " local dgz=0\n";
    kvm += " for " + kq1 + "=1,#" + kKsec + " do dgz=(dgz*" + std::to_string(g_bc.cmM) + "+" + vCk + "(" + kKsec + "[" +
           kq1 + "][3],(" + vK + "[1]+" + kq1 + "*" + std::to_string(g_bc.mc) + ")%4294967296)+" + kq1 + ")%4294967296 end\n";
    kvm += " if dgz~=ag2 then return nil end\n";
    kvm += " local " + kKsk + "=" + vMx + "(((" + vK + "[1]+" + vK + "[3])%2147483647+" + vEf + ")%2147483647,sidx*2+9)\n";
    kvm += " local " + kKin + "=" + kKx + "(" + kKsec + "[sidx][3]," + kKsk + ")\n";
    kvm += " if not " + kKin + " then return nil end\n";
    kvm += " local " + kPc + "={}\n";
    kvm += " local function " + kPr + "(pi)\n";
    kvm += "  local P=" + kPc + "[pi] if P then return P end\n";
    kvm += "  local d=" + kKin + "\n";
    kvm += "  local cur=1\n";
    kvm += "  if #d<4 then return nil end\n";
    kvm += "  local np=" + vByt + "(d,1)*256+" + vByt + "(d,2)\n";
    kvm += "  if pi<1 or pi>np then return nil end\n";
    kvm += "  local wd=" + vByt + "(d,3)\n";
    kvm += "  if wd<1 then return nil end\n";
    kvm += "  local off=4\n";
    kvm += "  local P2\n";
    kvm += "  for z2=1,np do\n";
    kvm += "   if off+9>#d then return nil end\n";
    kvm += "   local ni=" + vByt + "(d,off)*256+" + vByt + "(d,off+1) off=off+2\n";
    kvm += "   local nc=" + vByt + "(d,off)*256+" + vByt + "(d,off+1) off=off+2\n";
    kvm += "   local nr=" + vByt + "(d,off) off=off+1\n";
    kvm += "   local pk=" + vByt + "(d,off)*16777216+" + vByt + "(d,off+1)*65536+" +
           vByt + "(d,off+2)*256+" + vByt + "(d,off+3) off=off+4\n";
    kvm += "   local kt={}\n";
    kvm += "   for q=1,nc do if off+3>#d then return nil end kt[q]=" + vByt + "(d,off)*16777216+" + vByt +
           "(d,off+1)*65536+" + vByt + "(d,off+2)*256+" + vByt +
           "(d,off+3) off=off+4 end\n";
    kvm += "   if z2==pi then\n";
    kvm += "    local mr={} for q=1,nr do mr[q]=q end\n";
    kvm += "    local ws=pk\n";
    kvm += "    for q=nr,2,-1 do ws=" + vLm + "(ws) local wj=1+ws%q mr[q],mr[wj]=mr[wj],mr[q] end\n";
    kvm += "    local z1={} local z2={}\n";
    kvm += "    for q=1,nr do local zf=(pk+q*@KME@)%2147483646 local za=" + vMx + "(pk,q*17+3)%2147483646 z1[q]=za z2[q]=(zf-za+2147483646)%2147483646 end\n";
    kvm += "    P2={ni=ni,kt=kt,pk=pk,base=off,mr=mr,z1=z1,z2=z2,wd=wd}\n";
    kvm += "   end\n";
    kvm += "   off=off+ni*wd\n";
    kvm += "  end\n";
    kvm += "  " + kPc + "[pi]=P2\n";
    kvm += "  return P2\n";
    kvm += " end\n";
    kvm += " local function " + kKvmr + "(pi)\n";
    kvm += "  local P=" + kPr + "(pi) if not P then " + vWp + "() end\n";
    kvm += "  local d=" + kKin + "\n";
    kvm += "  local R={} local mr=P.mr local kt=P.kt local pk=P.pk\n";
    kvm += "  local ni=P.ni local base=P.base\n";
    kvm += "  local st={r=R,mr=mr,kt=kt,st=" + kSt + ",z1=P.z1,z2=P.z2}\n";
    kvm += "  local wd=P.wd\n";
    kvm += "  local pc=1\n";
    kvm += "  while pc and pc>=1 do\n";
    kvm += "   if pc>ni then " + vWp + "() end\n";
    kvm += "   local o=base+(pc-1)*wd\n";
    kvm += "   if o+wd-1>#d then " + vWp + "() end\n";
    kvm += "   local s0=" + vMx + "(pk,pc)\n";
    kvm += "   if s0<1 then s0=s0+2147483646 end\n";
    kvm += "   local s1=" + vLm + "(s0) local s2=" + vLm + "(s1)\n";
    kvm += "   local c1=" + vBx + "(" + vByt + "(d,o),s1%256)\n";
    kvm += "   local c2=" + vBx + "(" + vByt + "(d,o+1)," + vFlr + "(s1/256)%256)\n";
    kvm += "   local c3=" + vBx + "(" + vByt + "(d,o+2)," + vFlr + "(s1/65536)%256)\n";
    kvm += "   local c4=" + vBx + "(" + vByt + "(d,o+3)," + vFlr + "(s1/16777216)%256)\n";
    kvm += "   local c5=" + vBx + "(" + vByt + "(d,o+4),s2%256)\n";
    kvm += "   local c6,c7\n";
    kvm += "   if wd>5 then c6=" + vBx + "(" + vByt + "(d,o+5)," + vFlr + "(s2/256)%256) end\n";
    kvm += "   if wd>6 then c7=" + vBx + "(" + vByt + "(d,o+6)," + vLm + "(s2)%256) end\n";
    kvm += "   local op,a8,b16,c8\n";
    kvm += "   if lay==0 then op=c1 a8=c2 b16=c3*256+c4 c8=c5";
    kvm += " elseif lay==1 then";
    kvm += "    if wd==5 then op=c4 a8=c2 b16=c3*256+c5 c8=c1";
    kvm += "    else op=c5 a8=c3 b16=c4*256+c6 c8=c1 end";
    kvm += " else";
    kvm += "    if wd==5 then op=c3 a8=c5 b16=c1*256+c4 c8=c2";
    kvm += "    elseif wd==6 then op=c4 a8=c6 b16=c1*256+c5 c8=c2";
    kvm += "    else op=c5 a8=c7 b16=c2*256+c6 c8=c3 end";
    kvm += "   end\n";
    kvm += "   if not " + kHh + "[op] then " + vWp + "() end\n";
    kvm += "   if " + kJt + "[op]==1 then\n";
    kvm += "    local jm=" + vMx + "(pk,pc*4+4)%65536\n";
    kvm += "    b16=(b16-jm)%65536\n";
    kvm += "    if b16>=32768 then b16=b16-65536 end\n";
    kvm += "   end\n";
    kvm += "   pc=pc+1\n";
    kvm += "   pc=" + kHh + "[op](st,{[2]=a8,[3]=b16,[4]=c8},pc)\n";
    kvm += "  end\n";

    kvm += "  if pc~=-1 then " + vWp + "() end\n";
    kvm += " end\n";
    kvm += " return " + kSt + "," + kKvmr + "\n";
    kvm += "end\n";
    kvm += "local " + kD1 + "=" + vD8 + "(\"" + kB85text + "\") if not " + kD1 + " then " + vWp + "() end\n";
    kvm += "local " + kD2 + "=" + vD8 + "(\"" + kB85ghost + "\") if not " + kD2 + " then " + vWp + "() end\n";
    kvm += "local " + kSt + "," + kKvmr + "=" + kZ + "(" + kD1 + "," +
           std::to_string(b.kSIdx) + "," + std::to_string(b.kLay) + "," + std::to_string(b.kW) + "," + std::to_string(kAggReal) + ")\n";
    kvm += "local " + kS2 + "," + kR2 + "=" + kZ + "(" + kD2 + "," +
           std::to_string(b.kSIdxG) + "," + std::to_string(b.kLayG) + "," + std::to_string(b.kWG) + "," + std::to_string(kAggGhost) + ")\n";
    kvm += "if not " + kSt + " or not " + kS2 + " then " + vWp + "() end\n";
    kvm += kKvmr + "(" + std::to_string(b.kPA) + ") " + kR2 + "(" + std::to_string(b.kPA) + ")\n";
    kvm += "if " + kSt + "[3]~=" + std::to_string(b.kG1) + " or not " + kSt +
           "[1] or " + kS2 + "[3]~=" + std::to_string(b.kG1) + " or " + kS2 +
           "[1]~=" + kSt + "[1] then " + vWp + "() end\n";
    kvm += "local vk=" + kSt + "[1]\n";
    kvm += vSbx + "," + vSix + "=" + vMk2 + "(vk)\n";
    kvm += "local mb=" + vDm + "(m0[3],vk)\n";
    kvm += "if not mb or #mb<20 then " + vWp + "() end\n";
    kvm += "local mc=" + vByt + "(mb,1)*16777216+" + vByt + "(mb,2)*65536+" +
           vByt + "(mb,3)*256+" + vByt + "(mb,4)\n";
    kvm += "if mc~=#" + vSs + " then " + vWp + "() end\n";
    kvm += "local mg=" + vByt + "(mb,17)*16777216+" + vByt + "(mb,18)*65536+" +
           vByt + "(mb,19)*256+" + vByt + "(mb,20)\n";
    kvm += "if " + vCk + "(" + vSub + "(" + vB + ",m0[1]+9)," + vK + "[1])~=mg then " + vWp + "() end\n";
    kvm += vB + "=nil\n";
    kvm += kSt + "[3]=nil " + kS2 + "[3]=nil\n";
    kvm += "local " + vAn + "=" + kSt + "[2]\n";
    kvm += kSt + "[4]=" + vCku + "[mc-1] or 0\n";
    kvm += kS2 + "[4]=" + kSt + "[4]\n";
    kvm += kKvmr + "(" + std::to_string(b.kPB) + ") " + kR2 + "(" + std::to_string(b.kPB) + ")\n";
    kvm += "if not " + kSt + "[5] or " + kS2 + "[5]~=" + kSt + "[5] then " + vWp + "() end\n";
    kvm += "local vkc=" + kSt + "[5]\n";
    kvm += kSt + "[1]=nil " + kS2 + "[1]=nil " + kSt + "[2]=nil " + kS2 + "[2]=nil " + kSt + "[4]=nil " + kS2 + "[4]=nil " + kSt + "[5]=nil " + kS2 + "[5]=nil\n";
    kvm += "local vb=" + vDm + "(" + vSs + "[mc][3],vkc)\n";
    kvm += "if not vb then " + vWp + "() end\n";
    kvm += "local nv=" + vByt + "(vb,1)*256+" + vByt + "(vb,2)\n";
    kvm += "if nv<1 or #vb<nv*11+8 then " + vWp + "() end\n";
    kvm += "local " + vVd + "={} local " + vV2 + "={} local " + vPd + " local " +
           vPv + " local " + vPe + " local " + vCk3 + "={} local " + vKep + "={}\n";
    kvm += "for i=1,nv do local p=(i-1)*4 " + vVd + "[i]=" + vByt + "(vb,p+3)*16777216+" +
           vByt + "(vb,p+4)*65536+" + vByt + "(vb,p+5)*256+" + vByt + "(vb,p+6) end\n";
    kvm += "local pp=2+nv*4\n";
    kvm += vPd + "=" + vByt + "(vb,pp+1)*16777216+" + vByt + "(vb,pp+2)*65536+" +
           vByt + "(vb,pp+3)*256+" + vByt + "(vb,pp+4)\n";
    kvm += vPv + "=" + vByt + "(vb,pp+5)*256+" + vByt + "(vb,pp+6)\n";
    kvm += "local px=pp+6\n";
    kvm += "for i=1,nv do " + vV2 + "[i]=" + vByt + "(vb,px+1)*256+" + vByt +
           "(vb,px+2) px=px+2 end\n";
    kvm += "for i=1,nv do " + vCk3 + "[i]=" + vByt + "(vb,px+1)*16777216+" + vByt +
           "(vb,px+2)*65536+" + vByt + "(vb,px+3)*256+" + vByt + "(vb,px+4) px=px+4 end\n";
    kvm += "for i=1,nv do " + vKep + "[i]=" + vByt + "(vb,px+1) px=px+1 end\n";
    kvm += kSt + "[7]=" + vPd + " " + kS2 + "[7]=" + vPd + "\n";
    kvm += kSt + "[8]=" + vAn + " " + kS2 + "[8]=" + vAn + "\n";
    kvm += "if " + vPv + ">2 then " + kSt + "[8]=" + vCku + "[" + vPv +
           "-1] " + kS2 + "[8]=" + kSt + "[8] end\n";
    kvm += kKvmr + "(" + std::to_string(b.kPC) + ") " + kR2 + "(" + std::to_string(b.kPC) + ")\n";
    kvm += "if not " + kSt + "[9] or " + kS2 + "[9]~=" + kSt + "[9] then " + vWp + "() end\n";
    kvm += vPe + "=" + kSt + "[9]\n";

    kvm += kSt + "[7]=nil " + kS2 + "[7]=nil " + kSt + "[8]=nil " + kS2 + "[8]=nil\n";
    kvm = renameIdents(kvm);

    {
        const std::string rnHead = "@RN@=function(P,uv,st,...)";
        size_t p0 = tmplT.find(rnHead);
        size_t pEnd = tmplT.find("@JK3@", p0);
        if (p0 != std::string::npos && pEnd != std::string::npos) {
            std::string body = tmplT.substr(p0, pEnd - p0);
            std::string bodyA = body;
            std::string bodyB = body;
            std::string bodyC = body;
            {
                const std::string rep = "@HOTDISP@";
                size_t hp = bodyB.find(rep);
                if (hp != std::string::npos)
                    bodyB.replace(hp, rep.size(), "@HOTDISP2@");
                bodyB.replace(0, rnHead.size(), "@RNB@=function(P,uv,st,...)");
            }
            {
                const std::string rep = "@HOTDISP@";
                size_t hp = bodyC.find(rep);
                if (hp != std::string::npos)
                    bodyC.replace(hp, rep.size(), "@HOTDISP3@");
                bodyC.replace(0, rnHead.size(), "@RNC@=function(P,uv,st,...)");
            }
            bodyA.replace(0, rnHead.size(), "@RNA@=function(P,uv,st,...)");
            std::string sel = "@RN@=function(P,uv,st,...) local r3=(st.nc+@RNS@)%3 if r3==0 then return @RNA@(P,uv,st,...) end if r3==1 then return @RNB@(P,uv,st,...) end return @RNC@(P,uv,st,...) end\n";
            tmplT.replace(p0, pEnd - p0, bodyA + bodyB + bodyC + sel);
        }
    }

    if (std::getenv("EXF_TMPLDBG")) {
        std::ofstream tf("/tmp/tmpl_in.txt"); tf << tmplT;
        std::ofstream tf2("/tmp/tmpl_ren.txt"); tf2 << renameIdents(tmplT);
    }
    {

        if (b.usesCo) {
            const std::string head = " local ok2,er2\n local function dspLoop()\n  while true do";
            const std::string tail = " end\n ok2,er2=@XP@(function() return dspLoop() end,function(e)\n  for kk in pairs(code) do code[kk]=nil end\n  fr.jc=false\n  fr.vo=false\n  fr.halt=nil\n  return e\n end)\n if not ok2 then @ERR@(er2,0) end";

            int nrm = 0;
            for (;;) {
                size_t hp2 = tmplT.find(head);
                if (hp2 == std::string::npos) break;
                tmplT.replace(hp2, head.size(), " while true do");
                ++nrm;
            }
            for (;;) {
                size_t tp2 = tmplT.find(tail);
                if (tp2 == std::string::npos) break;
                tmplT.replace(tp2, tail.size(), "");
                ++nrm;
            }
            if (std::getenv("EXF_TMPLDBG") && nrm == 0)
                std::fprintf(stderr, "EXF-18 guard MISS: no wrapper found\n");
        }
    }
    std::string tmpl = renameIdents(tmplT);
    double e2 = tick2();

    struct HDef { int opid; std::string code; };
    std::vector<HDef> defs;
    auto isHot = [](int canon) {
        switch (canon) {
            case VOP_MOVE: case VOP_LOADK: case VOP_LOADINT: case VOP_GETGLOBAL:
            case VOP_GETT: case VOP_GETT_K: case VOP_SETT: case VOP_SETT_K:
            case VOP_ADD: case VOP_SUB: case VOP_MUL: case VOP_DIV:
            case VOP_CALL: case VOP_CALLM: case VOP_SCALL: case VOP_GETGF:
            case VOP_JMP: case VOP_IFEQ: case VOP_IFNE: case VOP_IFLT:
            case VOP_IFLE: case VOP_IFGT: case VOP_IFGE: case VOP_JIFF:
            case VOP_JIFT: case VOP_DISPATCH: case VOP_SELF: case VOP_FORPREP:
            case VOP_FORLOOP: case VOP_RET: case VOP_RETM: case VOP_TAILCALL:
            case VOP_MCALL: case VOP_GCALL: case VOP_MTAIL: case VOP_GTAIL:
            case VOP_KRET: case VOP_CRET: case VOP_SCT: case VOP_CRTM:
            case VOP_IFEK: case VOP_IFNK: case VOP_FLEQ: case VOP_FLNE:
            case VOP_FLLT: case VOP_FLLE: case VOP_FLGT: case VOP_FLGE:
            case VOP_TSETK: case VOP_TGET2: case VOP_KARITH: case VOP_MVSETK:
            case VOP_STATEJMP:
            case VOP_RSUBK: case VOP_RDIVK: case VOP_RPOWK:
            case VOP_ADDI: case VOP_SUBI: case VOP_MULI:
            case VOP_IFLTK: case VOP_IFLEK: case VOP_IFGTK: case VOP_IFGEK:
            case VOP_IFKLT: case VOP_IFKLE: case VOP_IFKGT: case VOP_IFKGE:
            case VOP_CALL1: case VOP_CALL2: case VOP_CALL3:
            case VOP_RET0: case VOP_RET1:
            case VOP_GETTK: case VOP_GETTRK: case VOP_SETTRK:
            case VOP_NEWTAB_LIST:
            case VOP_LOAD2K: case VOP_MOVE2:
            case VOP_CONCAT2: case VOP_CONCAT3: case VOP_CONCATK:
            case VOP_GETT_I: case VOP_SETT_I:
            case VOP_FORPREP1: case VOP_FORLOOP1:
                return true;
            default:
                return false;
        }
    };
    auto rep1 = [](std::string s, const std::string& f, const std::string& r) {
        size_t p = 0;
        while ((p = s.find(f, p)) != std::string::npos) {
            s.replace(p, f.size(), r);
            p += r.size();
        }
        return s;
    };
    auto repNames = [&](std::string s) {
        s = rep1(s, "P.kids[", "P[" + fKid + "][");
        s = rep1(s, "P.kse[", "P[" + fKs + "][");
        s = rep1(s, "P.k[", "P[" + fK + "][");
        s = rep1(s, "fr.P.fl[", "fr.P[" + fFl + "][");
        s = rep1(s, "cp.uv[", "cp[" + fUv + "][");
        s = rep1(s, "#cp.uv", "#cp[" + fUv + "]");
        return s;
    };
    auto repSlots = [&](std::string s, const std::array<int, 5>& sl) {
        s = rep1(s, "ins[2]", "\x01""A\x01");
        s = rep1(s, "ins[3]", "\x01""B\x01");
        s = rep1(s, "ins[4]", "\x01""C\x01");
        s = rep1(s, "ins[5]", "\x01""S\x01");
        s = rep1(s, "ins[6]", "\x01""K\x01");
        s = rep1(s, "\x01""A\x01", "ins[" + std::to_string(sl[0]) + "]");
        s = rep1(s, "\x01""B\x01", "ins[" + std::to_string(sl[1]) + "]");
        s = rep1(s, "\x01""C\x01", "ins[" + std::to_string(sl[2]) + "]");
        s = rep1(s, "\x01""S\x01", "ins[" + std::to_string(sl[3]) + "]");
        s = rep1(s, "\x01""K\x01", "ins[" + std::to_string(sl[4]) + "]");
        return s;
    };
    auto mkInto = [&](std::vector<HDef>& sink, int canon, bool withP, bool isHalt,
                      const std::string& body) {
        int opid = b.opId[canon];
        std::string c = "function(fr,r,m,ins,pc)";
        if (withP) c += " local P=fr.P";
        c += " ";

        bool hot = isHot(canon);
        bool decoyOp = canon >= VOP_DECOY0 && canon <= VOP_DECOY11;
        double p1 = (!hot && decoyOp) ? 1.0 : 0.0;
        if (rng.chance(p1)) {
            c += trapGuard("ins[2]");
        }
        if (!hot && decoyOp && rng.chance(0.45)) {
            c += trapGuard("ins[5]");
        }

        c += body;
        c += isHalt ? " return -1 end" : " return pc end";
        c = repNames(repSlots(c, opSlots[(size_t)canon]));
        sink.push_back({opid, c});
    };
    auto mk = [&](int canon, bool withP, bool isHalt, const std::string& body) {
        mkInto(defs, canon, withP, isHalt, body);
    };
    const std::string PA = "\x01""A\x01";
    const std::string PBb = "\x01""B\x01";
    const std::string PCc = "\x01""C\x01";
    const std::string RA = "r[m[" + PA + "]]";
    const std::string RB = "r[m[" + PBb + "]]";
    const std::string RC = "r[m[" + PCc + "]]";
    const std::string KI = vKs + "(P,ins[6])";
    const std::string JRinline = "local j9 if fr.jc then j9=fr.jc[pc-1] end if j9==nil then j9=" + vJr + "(fr,pc,ins[7]) end pc=pc+j9";

    const std::string tmpN = N();
    auto pickForm = [&](const std::vector<std::string>& forms) {
        return forms[(size_t)rng.range(forms.size())];
    };
    mk(VOP_MOVE, false, false, pickForm({RA + "=" + RB, "do " + RA + "=" + RB + " end",
        "local " + tmpN + "=" + RB + " " + RA + "=" + tmpN}));
    mk(VOP_LOADNIL, false, false, pickForm({RA + "=nil", "do " + RA + "=nil end"}));
    mk(VOP_LOADTRUE, false, false, pickForm({RA + "=true", "do " + RA + "=true end"}));
    mk(VOP_LOADFALSE, false, false, pickForm({RA + "=false", "do " + RA + "=false end"}));
    mk(VOP_LOADINT, false, false, RA + "=ins[5]");
    mk(VOP_LOADK, true, false, RA + "=" + KI);

    mk(VOP_GETGLOBAL, true, false,
       "do local g8=fr.st.gm if g8 then local w8=g8[" + KI + "] if w8~=nil then " + RA +
           "=w8[1] else " + RA + "=" + vGnv + "(" + KI + ",fr) end else " + RA +
           "=" + vGnv + "(" + KI + ",fr) end end");
    mk(VOP_SETGLOBAL, true, false,

       b.sandboxGlobals
           ? "do local g9=fr.st if not g9.gm then g9.gm={} end g9.gm[" + KI + "]={" + RA + "} end"
           : "do local g9=fr.st if not g9.gm then g9.gm={} end g9.gm[" + KI + "]={" + RA +
                 "} " + vEnv + "[" + KI + "]=" + RA + " end");
    mk(VOP_GETUPVAL, false, false,
       "local c=fr.uv[ins[3]] local f=c.r if f then " + RA +
           "=f[c.m[c.idx]] else " + RA + "=c.v end");
    mk(VOP_SETUPVAL, false, false,
       "local c=fr.uv[ins[3]] if c.r then c.r[c.m[c.idx]]=" + RA +
           " else c.v=" + RA + " end");
    mk(VOP_GETT, false, false, pickForm({RA + "=" + RB + "[" + RC + "]",
        "local " + tmpN + "=" + RB + " " + RA + "=" + tmpN + "[" + RC + "]"}));
    mk(VOP_GETT_K, true, false, RA + "=" + RB + "[" + KI + "]");
    mk(VOP_SETT, false, false, pickForm({RB + "[" + RC + "]=" + RA,
        "do " + RB + "[" + RC + "]=" + RA + " end"}));
    mk(VOP_SETT_K, true, false, RB + "[" + KI + "]=" + RA);
    mk(VOP_NEWTABLE, false, false, RA + "={}");
    mk(VOP_SETLIST, false, false,
       "local t=" + RA + " local off=(ins[4]-1)*24 "
       "if ins[3]==0 then local m0=r[m[ins[2]+1]][" + vMk +
           "] local p9=ins[4] if p9>0 then p9=p9-1 else p9=#t end for i=1,m0.n do t[p9+i]=m0[i] end "
           "else for i=1,ins[3]-1 do t[off+i]=r[m[ins[2]+i]] end end");
    mk(VOP_SELF, true, false,
       "r[m[ins[2]+1]]=" + RB + " " + RA + "=" + RB + "[" + KI + "]");
    mk(VOP_CONCAT, false, false,
       "local x=" + RB + " for i=ins[3]+1,ins[4] do x=x..r[m[i]] end " + RA +
           "=x");
    mk(VOP_ADD, false, false, pickForm({RA + "=" + RB + "+" + RC, "do " + RA + "=" + RB + "+" + RC + " end"}));
    mk(VOP_SUB, false, false, pickForm({RA + "=" + RB + "-" + RC, "do " + RA + "=" + RB + "-" + RC + " end"}));
    mk(VOP_MUL, false, false, pickForm({RA + "=" + RB + "*" + RC, "do " + RA + "=" + RB + "*" + RC + " end"}));
    mk(VOP_DIV, false, false, pickForm({RA + "=" + RB + "/" + RC, RA + "=" + RB + "/(" + RC + ")"}));
    mk(VOP_MOD, false, false, pickForm({RA + "=" + RB + "%" + RC, RA + "=" + RB + "%(" + RC + ")"}));
    mk(VOP_POW, false, false, pickForm({RA + "=" + RB + "^" + RC, RA + "=" + RB + "^(" + RC + ")"}));
    mk(VOP_ADDK, true, false, pickForm({RA + "=" + RB + "+P.k[ins[6]]", "do " + RA + "=" + RB + "+P.k[ins[6]] end"}));
    mk(VOP_SUBK, true, false, pickForm({RA + "=" + RB + "-P.k[ins[6]]", RA + "=" + RB + "-(P.k[ins[6]])"}));
    mk(VOP_MULK, true, false, pickForm({RA + "=" + RB + "*P.k[ins[6]]", "do " + RA + "=" + RB + "*P.k[ins[6]] end"}));
    mk(VOP_DIVK, true, false, pickForm({RA + "=" + RB + "/P.k[ins[6]]", RA + "=" + RB + "/(P.k[ins[6]])"}));
    mk(VOP_MODK, true, false, pickForm({RA + "=" + RB + "%P.k[ins[6]]", RA + "=" + RB + "%(P.k[ins[6]])"}));
    mk(VOP_POWK, true, false, pickForm({RA + "=" + RB + "^P.k[ins[6]]", RA + "=" + RB + "^(P.k[ins[6]])"}));
    mk(VOP_UNM, false, false, pickForm({RA + "=-" + RB, "do " + RA + "=-" + RB + " end"}));
    mk(VOP_NOT, false, false, pickForm({RA + "=not " + RB, "do " + RA + "=not " + RB + " end"}));
    mk(VOP_LEN, false, false, pickForm({RA + "=#" + RB,
        "local " + tmpN + "=" + RB + " " + RA + "=#" + tmpN}));
    mk(VOP_JMP, false, false, JRinline);
    mk(VOP_IFEQ, false, false, pickForm({"if " + RA + "==" + RB + " then " + JRinline + " end",
        "if (" + RA + "==" + RB + ") then " + JRinline + " end"}));
    mk(VOP_IFNE, false, false, pickForm({"if " + RA + "~=" + RB + " then " + JRinline + " end",
        "if (" + RA + "~=" + RB + ") then " + JRinline + " end"}));
    mk(VOP_IFLT, false, false, pickForm({"if " + RA + "<" + RB + " then " + JRinline + " end", "if " + RB + ">" + RA + " then " + JRinline + " end"}));
    mk(VOP_IFLE, false, false, pickForm({"if " + RA + "<=" + RB + " then " + JRinline + " end", "if " + RB + ">=" + RA + " then " + JRinline + " end"}));
    mk(VOP_IFGT, false, false, pickForm({"if " + RA + ">" + RB + " then " + JRinline + " end", "if " + RB + "<" + RA + " then " + JRinline + " end"}));
    mk(VOP_IFGE, false, false, pickForm({"if " + RA + ">=" + RB + " then " + JRinline + " end", "if " + RB + "<=" + RA + " then " + JRinline + " end"}));
    mk(VOP_IFEK, true, false, pickForm({"if " + RA + "==" + KI + " then " + JRinline + " end", "if (" + RA + "==" + KI + ") then " + JRinline + " end"}));
    mk(VOP_IFNK, true, false, pickForm({"if " + RA + "~=" + KI + " then " + JRinline + " end", "if " + KI + "~=" + RA + " then " + JRinline + " end"}));
    mk(VOP_FLEQ, false, false, pickForm({"if #" + RA + "==" + RB + " then " + JRinline + " end", "if " + RB + "==#" + RA + " then " + JRinline + " end"}));
    mk(VOP_FLNE, false, false, pickForm({"if #" + RA + "~=" + RB + " then " + JRinline + " end", "if " + RB + "~=#" + RA + " then " + JRinline + " end"}));
    mk(VOP_FLLT, false, false, pickForm({"if #" + RA + "<" + RB + " then " + JRinline + " end", "if " + RB + ">#" + RA + " then " + JRinline + " end"}));
    mk(VOP_FLLE, false, false, pickForm({"if #" + RA + "<=" + RB + " then " + JRinline + " end", "if " + RB + ">=#" + RA + " then " + JRinline + " end"}));
    mk(VOP_FLGT, false, false, pickForm({"if #" + RA + ">" + RB + " then " + JRinline + " end", "if " + RB + "<#" + RA + " then " + JRinline + " end"}));
    mk(VOP_FLGE, false, false, pickForm({"if #" + RA + ">=" + RB + " then " + JRinline + " end", "if " + RB + "<=#" + RA + " then " + JRinline + " end"}));
    mk(VOP_JIFF, false, false, "if not " + RA + " then " + JRinline + " end");
    mk(VOP_JIFT, false, false, "if " + RA + " then " + JRinline + " end");
    mk(VOP_CALL, false, false,
       "local f=" + RA + " local rt "
       "if ins[3]==0 then local m0=r[m[ins[2]+1]][" + vMk +
           "] rt=" + vPk + "(f(" + vUpk + "(m0,1,m0.n))) "
           "else rt=" + vPk + "(f(" + vUpk + "(" + vCra + "(r,m,ins[2]+1,ins[2]+ins[3]-1),1,ins[3]-1))) end "
           "if ins[4]==0 then " + RA + "={[" + vMk + "]=rt} "
           "else for i=1,ins[4]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mk(VOP_CALLM, false, false,
       "local f=" + RA + " local m0=r[m[ins[2]+ins[3]+1]][" + vMk +
           "] local ar=" + vCra + "(r,m,ins[2]+1,ins[2]+ins[3]) local w=ins[3] "
           "for i=1,m0.n do w=w+1 ar[w]=m0[i] end "
           "local rt=" + vPk + "(f(" + vUpk + "(ar,1,w))) "
           "if ins[4]==0 then " + RA + "={[" + vMk + "]=rt} "
           "else for i=1,ins[4]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mk(VOP_TAILCALL, false, true,
       "local f=" + RA + " fr.halt={t=1,f=f,a=" + vCra +
           "(r,m,ins[2]+1,ins[2]+ins[3]-1),n=ins[3]-1}");
    mk(VOP_RET, false, true,
       "if ins[3]==0 then fr.halt=" + RA + "[" + vMk + "] "
       "else local t=" + vCra + "(r,m,ins[2],ins[2]+ins[3]-2) t.n=ins[3]-1 fr.halt=t end");
    mk(VOP_RETM, false, true,
       "local t={} local w=0 for i=1,ins[3] do w=w+1 t[w]=r[m[ins[2]+i-1]] end "
       "local m0=r[m[ins[2]+ins[3]]][" + vMk + "] "
       "for i=1,m0.n do w=w+1 t[w]=m0[i] end t.n=w fr.halt=t");
    mk(VOP_VARARG, false, false,
       "if ins[3]==0 then " + RA + "={[" + vMk + "]=fr.va} else for i=1,ins[3]-1 do r[m[ins[2]+i-1]]=fr.va[i] end end");
    mk(VOP_VARARG1, false, false, pickForm({RA + "=fr.va[1]",
        "local " + tmpN + "=fr.va " + RA + "=" + tmpN + "[1]"}));
    mk(VOP_SPILL, false, false,
       "local m0=" + RA + "[" + vMk +
           "] for i=1,ins[3] do r[m[ins[2]+i-1]]=m0[i] end");
    mk(VOP_CLOSURE, true, false,
       "local vo=fr.vo if not vo then vo={} fr.vo=vo end "
       "local cp=" + vPl + "(P.kids[ins[6]],P.st) local cells={} "
       "for i=1,#cp.uv do local ds=cp.uv[i] "
       "if ds[1]==0 then local rg=ds[2] local c0=vo[rg] "
       "if not c0 then c0={v=r[m[rg]],r=r,m=m,idx=rg} vo[rg]=c0 end "
       "cells[i]=c0 else cells[i]=fr.uv[ds[2]] end end " + RA +
           "=" + vMc + "(cp,cells)");
    mk(VOP_CLOSE, false, false, vCl + "(fr,ins[2])");
    mk(VOP_FORPREP, false, false,
       std::string("if r[m[ins[2]+2]]==0 then " + vErr + "(" + escStr("for step is zero") +
                   ") end ") +
           RA + "=" + RA + "-r[m[ins[2]+2]] " + JRinline);
    mk(VOP_FORLOOP, false, false,
       "local st=r[m[ins[2]+2]] " + RA + "=" + RA + "+st "
       "if st>0 then if " + RA + "<=r[m[ins[2]+1]] then r[m[ins[2]+3]]=" + RA +
       " " + JRinline + " end "
       "elseif st<0 then if " + RA + ">=r[m[ins[2]+1]] then r[m[ins[2]+3]]=" +
       RA + " " + JRinline + " end end");
    mk(VOP_TFOR, false, false,
       "local f=" + RA + " local rs=" + vPk +
           "(f(r[m[ins[2]+1]],r[m[ins[2]+2]])) "
           "for i=1,ins[4] do r[m[ins[2]+2+i]]=rs[i] end "
           "if r[m[ins[2]+3]]~=nil then r[m[ins[2]+2]]=r[m[ins[2]+3]] else " + JRinline + " end");
    mk(VOP_DISPATCH, false, false, "pc=fr.P.fl[" + RA + "]");
    mk(VOP_GETGF, true, false,

       RA + "=" + vGnv + "(" + KI + ",fr)[" + vKs + "(P,ins[3])]");
    mk(VOP_SCALL, true, false,
       "r[m[ins[2]+1]]=" + RB + " " + RA + "=" + RB + "[" + KI +
       "] local f=" + RA + " local rt "
       "if ins[5]==2 then rt=" + vPk + "(f(r[m[ins[2]+1]])) else rt=" + vPk +
       "(f(r[m[ins[2]+1]]," + vUpk + "(" + vCra + "(r,m,ins[2]+2,ins[2]+ins[5]-1),1,ins[5]-2))) end "
       "if ins[4]==0 then " + RA + "={[" + vMk + "]=rt} "
       "else for i=1,ins[4]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mk(VOP_RETK, true, true, "fr.halt={n=1," + KI + "}");
    mk(VOP_MCALL, true, false,
       "r[m[ins[2]]]=r[m[ins[3]]][" + KI + "] local f=" + RA + " local rt "
       "if ins[5]==0 then local m0=r[m[ins[2]+1]][" + vMk +
           "] rt=" + vPk + "(f(" + vUpk + "(m0,1,m0.n))) "
           "else rt=" + vPk + "(f(" + vUpk + "(" + vCra + "(r,m,ins[2]+1,ins[2]+ins[5]-1),1,ins[5]-1))) end "
           "if ins[4]==0 then " + RA + "={[" + vMk + "]=rt} "
           "else for i=1,ins[4]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mk(VOP_GCALL, true, false,
       RA + "=" + vGnv + "(" + KI + ",fr)[" + vKs + "(P,ins[3])] local f=" + RA +
           " local rt "
           "if ins[5]==0 then local m0=r[m[ins[2]+1]][" + vMk +
           "] rt=" + vPk + "(f(" + vUpk + "(m0,1,m0.n))) "
           "else rt=" + vPk + "(f(" + vUpk + "(" + vCra + "(r,m,ins[2]+1,ins[2]+ins[5]-1),1,ins[5]-1))) end "
           "if ins[4]==0 then " + RA + "={[" + vMk + "]=rt} "
           "else for i=1,ins[4]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mk(VOP_MTAIL, true, true,
       "r[m[ins[2]]]=r[m[ins[3]]][" + KI + "] local ar=" + vCra +
       "(r,m,ins[2]+1,ins[2]+ins[5]-1) "
       "fr.halt={t=1,f=r[m[ins[2]]],a=ar,n=ins[5]-1}");
    mk(VOP_GTAIL, true, true,
       RA + "=" + vGnv + "(" + KI + ",fr)[" + vKs + "(P,ins[3])] local ar=" + vCra +
       "(r,m,ins[2]+1,ins[2]+ins[5]-1) "
       "fr.halt={t=1,f=" + RA + ",a=ar,n=ins[5]-1}");
    mk(VOP_KRET, true, true,
       "fr.halt={n=1," + RB + "[" + KI + "]}");
    mk(VOP_CRET, false, true,
       "local f=" + RA + " local rt "
       "if ins[3]==0 then local m0=r[m[ins[2]+1]][" + vMk +
           "] rt=" + vPk + "(f(" + vUpk + "(m0,1,m0.n))) "
           "else rt=" + vPk + "(f(" + vUpk + "(" + vCra + "(r,m,ins[2]+1,ins[2]+ins[3]-1),1,ins[3]-1))) end "
           "fr.halt=rt");
    mk(VOP_SCT, true, true,
       "r[m[ins[2]+1]]=r[m[ins[3]]] " + RA + "=r[m[ins[3]]][" + KI +
           "] local ar=" + vCra + "(r,m,ins[2]+1,ins[2]+ins[5]-1) "
           "fr.halt={t=1,f=" + RA + ",a=ar,n=ins[5]-1}");
    mk(VOP_CRTM, false, true,
       "local f=" + RA + " local m0=r[m[ins[2]+ins[3]+1]][" + vMk +
           "] local ar=" + vCra + "(r,m,ins[2]+1,ins[2]+ins[3]) local w=ins[3] "
           "for i=1,m0.n do w=w+1 ar[w]=m0[i] end "
           "fr.halt=" + vPk + "(f(" + vUpk + "(ar,1,w)))");
    mk(VOP_TSETK, true, false,
       "r[m[" + PA + "]][" + KI + "]=" + vKs + "(P,ins[3])");
    mk(VOP_TGET2, true, false,
       "r[m[" + PA + "]]=r[m[" + PCc + "]][" + vKs + "(P,ins[3])] r[m[" + PA + "]+1]=r[m[" + PCc + "]][" + KI + "]");
    mk(VOP_TGETC, true, false,
       "r[m[" + PA + "]]=r[m[" + PCc + "]][" + vKs + "(P,ins[3])][" + KI + "]");
    mk(VOP_TADDK, true, false,
       std::string("local x=r[m[") + PCc + "]][" + vKs + "(P,ins[3])] local w5=" + KI +
       " local s5=ins[5] " +
       (rng.chance(0.5)
           ? "if s5==1 then x=x+w5 elseif s5==2 then x=x-w5 elseif s5==3 then x=x*w5 "
           : "if s5==1 then x=x+w5 elseif s5==2 then x=x-w5 elseif s5==3 then x=x*w5 ") +
       "elseif s5==4 then x=x/w5 elseif s5==5 then x=x%w5 elseif s5==6 then x=x^w5 "
       "elseif s5==7 then x=w5-x elseif s5==8 then x=w5/x else x=w5^x end "
       "r[m[" + PA + "]]=x");
    mk(VOP_KARITH, true, false,
       "local x=r[m[" + PCc + "]] local s5=ins[5]-1 local w5=" + vKs + "(P,ins[3]) local q1=s5-s5%6 "
       "if q1==0 then x=x+w5 elseif q1==6 then x=x-w5 elseif q1==12 then x=x*w5 elseif q1==18 then x=x/w5 elseif q1==24 then x=x%w5 else x=x^w5 end "
       "local m6=s5%6 "
       "if m6==0 then x=x+" + KI + " elseif m6==1 then x=x-" + KI + " elseif m6==2 then x=x*" + KI + " elseif m6==3 then x=x/" + KI + " elseif m6==4 then x=x%" + KI + " else x=x^" + KI + " end "
       "r[m[" + PA + "]]=x");
    mk(VOP_MVSETK, true, false,
       "r[m[" + PA + "]][" + KI + "]=r[m[" + PBb + "]]");
    mk(VOP_RSUBK, true, false, RA + "=" + KI + "-" + RB);
    mk(VOP_RDIVK, true, false, RA + "=" + KI + "/" + RB);
    mk(VOP_RPOWK, true, false, RA + "=" + KI + "^" + RB);
    mk(VOP_ADDI, false, false, RA + "=" + RB + "+ins[5]");
    mk(VOP_SUBI, false, false, RA + "=" + RB + "-ins[5]");
    mk(VOP_MULI, false, false, RA + "=" + RB + "*ins[5]");
    mk(VOP_IFLTK, true, false, "if " + RA + "<" + KI + " then " + JRinline + " end");
    mk(VOP_IFLEK, true, false, "if " + RA + "<=" + KI + " then " + JRinline + " end");
    mk(VOP_IFGTK, true, false, "if " + RA + ">" + KI + " then " + JRinline + " end");
    mk(VOP_IFGEK, true, false, "if " + RA + ">=" + KI + " then " + JRinline + " end");
    mk(VOP_IFKLT, true, false, "if " + KI + "<" + RA + " then " + JRinline + " end");
    mk(VOP_IFKLE, true, false, "if " + KI + "<=" + RA + " then " + JRinline + " end");
    mk(VOP_IFKGT, true, false, "if " + KI + ">" + RA + " then " + JRinline + " end");
    mk(VOP_IFKGE, true, false, "if " + KI + ">=" + RA + " then " + JRinline + " end");
    mk(VOP_CALL1, false, false,
       "local f=" + RA + " local rt=" + vPk + "(f(r[m[ins[2]+1]])) "
       "if ins[3]==0 then " + RA + "={[" + vMk + "]=rt} "
       "else for i=1,ins[3]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mk(VOP_CALL2, false, false,
       "local f=" + RA + " local rt=" + vPk + "(f(r[m[ins[2]+1]],r[m[ins[2]+2]])) "
       "if ins[3]==0 then " + RA + "={[" + vMk + "]=rt} "
       "else for i=1,ins[3]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mk(VOP_CALL3, false, false,
       "local f=" + RA + " local rt=" + vPk + "(f(r[m[ins[2]+1]],r[m[ins[2]+2]],r[m[ins[2]+3]])) "
       "if ins[3]==0 then " + RA + "={[" + vMk + "]=rt} "
       "else for i=1,ins[3]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mk(VOP_RET0, false, true, "fr.halt={n=0}");
    mk(VOP_RET1, false, true, "fr.halt={n=1," + RA + "}");
    mk(VOP_GETTK, true, false, RA + "=" + RB + "[" + KI + "][" + RC + "]");
    mk(VOP_GETTRK, true, false, RA + "=" + RB + "[" + RC + "][" + KI + "]");
    mk(VOP_SETTRK, true, false, RB + "[" + RC + "]=" + KI);
    mk(VOP_NEWTAB_LIST, false, false,
       "local t={} for i=1,ins[3] do t[i]=r[m[ins[2]+i]] end r[m[ins[2]]]=t");
    mk(VOP_LOAD2K, true, false,
       RA + "=" + KI + " r[m[ins[2]+1]]=" + vKs + "(P,ins[3])");
    mk(VOP_MOVE2, false, false,
       RA + "=" + RB + " r[m[ins[2]+1]]=r[m[ins[3]+1]]");
    mk(VOP_CONCAT2, false, false, RA + "=" + RB + ".." + RC);
    mk(VOP_CONCAT3, false, false,
       RA + "=" + RB + "..r[m[ins[3]+1]]..r[m[ins[3]+2]]");
    mk(VOP_CONCATK, true, false, RA + "=" + RB + ".." + KI);
    mk(VOP_GETT_I, false, false, RA + "=" + RB + "[ins[5]]");
    mk(VOP_SETT_I, false, false, RB + "[ins[5]]=" + RA);
    mk(VOP_FORPREP1, false, false, RA + "=" + RA + "-1 " + JRinline);
    mk(VOP_FORLOOP1, false, false,
       RA + "=" + RA + "+1 if " + RA + "<=r[m[ins[2]+1]] then r[m[ins[2]+3]]=" +
       RA + " " + JRinline + " end");
    mk(VOP_STATEJMP, false, false, "pc=fr.P.fl[ins[5]]");
    for (int d = VOP_DECOY0; d <= VOP_DECOY11; ++d) {
        int sel = (int)rng.range(8);
        std::string body;
        if (sel == 0) body = RA + "=" + RB;
        else if (sel == 1) body = RA + "=" + RC;
        else if (sel == 2) body = RA + "=nil";
        else if (sel == 3) body = RA + "=not " + RB;
        else if (sel == 4) body = "local qx=" + RB + " " + RA + "=" + RB;
        else if (sel == 5) body = "if " + RB + "==nil then " + RA + "=nil else " + RA + "=" + RB + " end";
        else if (sel == 6) body = RA + "=" + RB + " local qy=" + RC;
        else if (sel == 7) body = RA + "=" + RC + " local qz=" + RB;
        else if (sel == 8) body = RA + "=" + RB + " " + RA + "=nil";
        else if (sel == 9) body = "do " + RA + "=" + RC + " end";
        else if (sel == 10) body = RA + "=#" + RB;
        else if (sel == 11) body = "local qw=" + RC + " " + RA + "=qw";
        else if (sel == 12) body = RA + "=" + RB + "==nil";
        else if (sel == 13) body = "if " + RC + " then " + RA + "=" + RB + " else " + RA + "=nil end";
        else if (sel == 14) body = RA + "=" + RB + " local qe=" + RB + " qe=nil";
        else body = "do local qr=" + RB + " " + RA + "=qr end";
        mk(d, false, false, body);
    }

    struct HotDef { int opid; std::string body; };
    std::vector<HotDef> hotDefs;
    auto mkin = [&](int canon, const std::string& body, bool halt = false) {
        if (!isHot(canon)) return;
        std::string c = repNames(repSlots(body, opSlots[(size_t)canon]));
        if (std::getenv("EXF_MKDBG")) {
            static std::ofstream md("/tmp/mkdbg.txt", std::ios::trunc);
            md << "canon=" << canon << " opid=" << b.opId[canon] << "\nIN : " << body
               << "\nOUT: " << c << "\n\n";
        }
        if (halt) c += " pc=-1 break";
        hotDefs.push_back({b.opId[canon], c});
    };
    mkin(VOP_MOVE, RA + "=" + RB);
    mkin(VOP_STATEJMP, "pc=fr.P.fl[ins[5]]");
    mkin(VOP_CALL1,
       "local f=" + RA + " local rt=" + vPk + "(f(r[m[ins[2]+1]])) "
       "if ins[3]==0 then " + RA + "={[" + vMk + "]=rt} "
       "else for i=1,ins[3]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mkin(VOP_ADD, RA + "=" + RB + "+" + RC);
    mkin(VOP_DISPATCH, "pc=fr.P.fl[" + RA + "]");
    mkin(VOP_IFLTK, "if " + RA + "<" + KI + " then " + JRinline + " end");
    mkin(VOP_RET1, "fr.halt={n=1," + RA + "}", true);
    mkin(VOP_GETT_K, RA + "=" + RB + "[" + KI + "]");
    mkin(VOP_JMP, JRinline);
    mkin(VOP_LOADINT, RA + "=ins[5]");
    mkin(VOP_GETT, RA + "=" + RB + "[" + RC + "]");
    mkin(VOP_IFEK, "if " + RA + "==" + KI + " then " + JRinline + " end");
    mkin(VOP_IFNK, "if " + RA + "~=" + KI + " then " + JRinline + " end");
    mkin(VOP_GETUPVAL,
       "local c=fr.uv[ins[3]] local f=c.r if f then " + RA +
           "=f[c.m[c.idx]] else " + RA + "=c.v end");
    mkin(VOP_ADDI, RA + "=" + RB + "+ins[5]");
    mkin(VOP_SUBI, RA + "=" + RB + "-ins[5]");
    mkin(VOP_ADDK, RA + "=" + RB + "+P.k[ins[6]]");
    mkin(VOP_SUBK, RA + "=" + RB + "-P.k[ins[6]]");
    mkin(VOP_MULK, RA + "=" + RB + "*P.k[ins[6]]");
    mkin(VOP_GETT_I, RA + "=" + RB + "[ins[5]]");
    mkin(VOP_JIFF, "if not " + RA + " then " + JRinline + " end");
    mkin(VOP_JIFT, "if " + RA + " then " + JRinline + " end");
    mkin(VOP_CALL2,
       "local f=" + RA + " local rt=" + vPk + "(f(r[m[ins[2]+1]],r[m[ins[2]+2]])) "
       "if ins[3]==0 then " + RA + "={[" + vMk + "]=rt} "
       "else for i=1,ins[3]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mkin(VOP_RET0, "fr.halt={n=0}", true);
    mkin(VOP_NOT, RA + "=not " + RB);
    mkin(VOP_MUL, RA + "=" + RB + "*" + RC);
    mkin(VOP_SUB, RA + "=" + RB + "-" + RC);
    mkin(VOP_MOD, RA + "=" + RB + "%" + RC);
    mkin(VOP_IFLT, "if " + RA + "<" + RB + " then " + JRinline + " end");
    mkin(VOP_IFLE, "if " + RA + "<=" + RB + " then " + JRinline + " end");
    mkin(VOP_IFGT, "if " + RA + ">" + RB + " then " + JRinline + " end");
    mkin(VOP_IFGE, "if " + RA + ">=" + RB + " then " + JRinline + " end");
    mkin(VOP_IFLEK, "if " + RA + "<=" + KI + " then " + JRinline + " end");
    mkin(VOP_IFGTK, "if " + RA + ">" + KI + " then " + JRinline + " end");
    mkin(VOP_IFGEK, "if " + RA + ">=" + KI + " then " + JRinline + " end");
    mkin(VOP_MCALL,
       "r[m[ins[2]]]=r[m[ins[3]]][" + KI + "] local f=" + RA + " local rt "
       "if ins[5]==0 then local m0=r[m[ins[2]+1]][" + vMk +
           "] rt=" + vPk + "(f(" + vUpk + "(m0,1,m0.n))) "
           "else rt=" + vPk + "(f(" + vUpk + "(" + vCra + "(r,m,ins[2]+1,ins[2]+ins[5]-1),1,ins[5]-1))) end "
           "if ins[4]==0 then " + RA + "={[" + vMk + "]=rt} "
           "else for i=1,ins[4]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mkin(VOP_SCALL,
       "r[m[ins[2]+1]]=" + RB + " " + RA + "=" + RB + "[" + KI +
       "] local f=" + RA + " local rt "
       "if ins[5]==2 then rt=" + vPk + "(f(r[m[ins[2]+1]])) else rt=" + vPk +
       "(f(r[m[ins[2]+1]]," + vUpk + "(" + vCra + "(r,m,ins[2]+2,ins[2]+ins[5]-1),1,ins[5]-2))) end "
       "if ins[4]==0 then " + RA + "={[" + vMk + "]=rt} "
       "else for i=1,ins[4]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    std::vector<HotDef> hotDefsB;
    auto mkinB = [&](int canon, const std::string& body, bool halt = false) {
        if (!isHot(canon)) return;
        std::string c = repNames(repSlots(body, opSlots[(size_t)canon]));
        if (halt) c += " pc=-1 break";
        hotDefsB.push_back({b.opId[canon], c});
    };
    mkinB(VOP_MOVE, RA + "=" + RB);
    mkinB(VOP_STATEJMP, "pc=fr.P.fl[ins[5]]");
    mkinB(VOP_CALL1,
       "local f=" + RA + " local rt=" + vPk + "(f(r[m[ins[2]+1]])) "
       "if ins[3]==0 then " + RA + "={[" + vMk + "]=rt} "
       "else for i=1,ins[3]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mkinB(VOP_ADD, RA + "=" + RB + "+" + RC);
    mkinB(VOP_DISPATCH, "pc=fr.P.fl[" + RA + "]");
    mkinB(VOP_IFLTK, "if " + RA + "<" + KI + " then " + JRinline + " end");
    mkinB(VOP_RET1, "fr.halt={n=1," + RA + "}", true);
    mkinB(VOP_GETT_K, RA + "=(" + RB + ")[" + KI + "]");
    mkinB(VOP_JMP, JRinline);
    mkinB(VOP_LOADINT, RA + "=ins[5]");
    mkinB(VOP_GETT, RA + "=" + RB + "[" + RC + "]");
    mkinB(VOP_IFEK, "if " + RA + "==" + KI + " then " + JRinline + " end");
    mkinB(VOP_IFNK, "if " + RA + "~=" + KI + " then " + JRinline + " end");
    mkinB(VOP_GETUPVAL,
       "local c=fr.uv[ins[3]] local f=c.r if not f then " + RA + "=c.v else " +
           RA + "=f[c.m[c.idx]] end");
    mkinB(VOP_ADDI, "local " + tmpN + "=ins[5] " + RA + "=" + RB + "+" + tmpN);
    mkinB(VOP_SUBI, RA + "=" + RB + "-ins[5]");
    mkinB(VOP_ADDK, RA + "=" + RB + "+P.k[ins[6]]");
    mkinB(VOP_SUBK, RA + "=" + RB + "-P.k[ins[6]]");
    mkinB(VOP_MULK, RA + "=" + RB + "*P.k[ins[6]]");
    mkinB(VOP_GETT_I, RA + "=(" + RB + ")[ins[5]]");
    mkinB(VOP_JIFF, "if not " + RA + " then " + JRinline + " end");
    mkinB(VOP_JIFT, "if " + RA + " then " + JRinline + " end");
    mkinB(VOP_CALL2,
       "local f=" + RA + " local rt=" + vPk + "(f(r[m[ins[2]+1]],r[m[ins[2]+2]])) "
       "if ins[3]~=0 then for i=1,ins[3]-1 do r[m[ins[2]+i-1]]=rt[i] end end "
       "if ins[3]==0 then " + RA + "={[" + vMk + "]=rt} end");
    mkinB(VOP_RET0, "fr.halt={n=0}", true);
    mkinB(VOP_NOT, RA + "=(not " + RB + ")");
    mkinB(VOP_MUL, RA + "=" + RB + "*" + RC);
    mkinB(VOP_SUB, RA + "=" + RB + "-" + RC);
    mkinB(VOP_MOD, RA + "=" + RB + "%(" + RC + ")");
    mkinB(VOP_IFLT, "if " + RB + ">" + RA + " then " + JRinline + " end");
    mkinB(VOP_IFLE, "if " + RB + ">=" + RA + " then " + JRinline + " end");
    mkinB(VOP_IFGT, "if " + RB + "<" + RA + " then " + JRinline + " end");
    mkinB(VOP_IFGE, "if " + RB + "<=" + RA + " then " + JRinline + " end");
    mkinB(VOP_IFLEK, "if " + KI + ">=" + RA + " then " + JRinline + " end");
    mkinB(VOP_IFGTK, "if " + KI + "<" + RA + " then " + JRinline + " end");
    mkinB(VOP_IFGEK, "if " + KI + "<=" + RA + " then " + JRinline + " end");
    mkinB(VOP_MCALL,
       "r[m[ins[2]]]=r[m[ins[3]]][" + KI + "] local f=" + RA + " local rt "
       "if ins[5]==0 then local m0=r[m[ins[2]+1]][" + vMk +
           "] rt=" + vPk + "(f(" + vUpk + "(m0,1,m0.n))) "
           "else rt=" + vPk + "(f(" + vUpk + "(" + vCra + "(r,m,ins[2]+1,ins[2]+ins[5]-1),1,ins[5]-1))) end "
           "if ins[4]==0 then " + RA + "={[" + vMk + "]=rt} "
           "else for i=1,ins[4]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    mkinB(VOP_SCALL,
       "r[m[ins[2]+1]]=" + RB + " " + RA + "=" + RB + "[" + KI +
       "] local f=" + RA + " local rt "
       "if ins[5]==2 then rt=" + vPk + "(f(r[m[ins[2]+1]])) else rt=" + vPk +
       "(f(r[m[ins[2]+1]]," + vUpk + "(" + vCra + "(r,m,ins[2]+2,ins[2]+ins[5]-1),1,ins[5]-2))) end "
       "if ins[4]==0 then " + RA + "={[" + vMk + "]=rt} "
       "else for i=1,ins[4]-1 do r[m[ins[2]+i-1]]=rt[i] end end");
    auto buildDisp = [&](const std::vector<HotDef>& hdefs, int dhvForce = -1) {
        std::string hd0;
        int dhv = dhvForce >= 0 ? dhvForce : (int)rng.range(3);
        if (dhv == 0 || hdefs.empty()) {
            int cform = (int)rng.range(3);
            for (size_t hi = 0; hi < hdefs.size(); ++hi) {
                if (hi == 0) hd0 += "if ";
                else hd0 += "elseif ";
                if (cform == 0) hd0 += "t==" + std::to_string(hdefs[hi].opid);
                else if (cform == 1) hd0 += std::to_string(hdefs[hi].opid) + "==t";
                else hd0 += "(t==" + std::to_string(hdefs[hi].opid) + ")";
                hd0 += " then " + hdefs[hi].body + "\n";
            }
            if (hd0.empty()) hd0 = "if t==-1 then\n";
            hd0 += "else pc=ins[8](fr,r,m,ins,pc) if pc==-1 then break end end";
        } else if (dhv == 1) {
            int mn = hdefs[0].opid, mx = mn;
            for (const auto& h : hdefs) {
                if (h.opid < mn) mn = h.opid;
                if (h.opid > mx) mx = h.opid;
            }
            std::vector<std::string> slots((size_t)(mx - mn + 1));
            std::vector<bool> used((size_t)(mx - mn + 1), false);
            for (const auto& h : hdefs) {
                slots[(size_t)(h.opid - mn)] = h.body;
                used[(size_t)(h.opid - mn)] = true;
            }
            bool first = true;
            for (size_t si2 = 0; si2 < slots.size(); ++si2) {
                if (!used[si2]) continue;
                hd0 += first ? "if t9==" : "elseif t9==";
                hd0 += std::to_string(si2) + " then " + slots[si2] + "\n";
                first = false;
            }
            hd0 += "else pc=ins[8](fr,r,m,ins,pc) if pc==-1 then break end end";
            hd0 = "do local t9=t-" + std::to_string(mn) + " " + hd0 + " end";
        } else {
            std::vector<HotDef> hd = hdefs;
            std::sort(hd.begin(), hd.end(), [](const HotDef& a, const HotDef& c) { return a.opid < c.opid; });
            size_t gi2 = 0;
            bool outerFirst = true;
            while (gi2 < hd.size()) {
                size_t take = 2 + (size_t)rng.range(3);
                if (gi2 + take > hd.size()) take = hd.size() - gi2;
                int lo = hd[gi2].opid, hi2 = hd[gi2 + take - 1].opid;
                std::string blk;
                bool f2 = true;
                for (size_t z = 0; z < take; ++z) {
                    blk += f2 ? "if t==" : "elseif t==";
                    blk += std::to_string(hd[gi2 + z].opid) + " then " + hd[gi2 + z].body + "\n";
                    f2 = false;
                }
                blk += "else pc=ins[8](fr,r,m,ins,pc) if pc==-1 then break end end ";
                hd0 += (outerFirst ? "if t>=" : "elseif t>=") + std::to_string(lo) +
                       " and t<=" + std::to_string(hi2) + " then " + blk;
                outerFirst = false;
                gi2 += take;
            }
            hd0 += "else pc=ins[8](fr,r,m,ins,pc) if pc==-1 then break end end";
        }
        return hd0;
    };
    int dhvSel = (int)rng.range(3);
    int dhvB = (dhvSel + 1 + (int)rng.range(2)) % 3;
    int dhvC = 3 - dhvSel - dhvB;
    double m1 = tick2();
    if (std::getenv("EXF_HOTPRE")) {
        std::ofstream hp2("/tmp/hotpre.txt");
        hp2 << buildDisp(hotDefs, dhvSel);
    }
    std::string hotdisp = renameIdents(buildDisp(hotDefs, dhvSel));
    std::string hotdisp2 = renameIdents(buildDisp(hotDefsB, dhvB));
    std::vector<HotDef> hotDefsC;
    hotDefsC.reserve(hotDefsB.size());
    for (const HotDef& h : hotDefsB) hotDefsC.push_back({h.opid, "do " + h.body + " end"});
    std::string hotdisp3 = renameIdents(buildDisp(hotDefsC, dhvC));
    {
        const std::string g1 = "function(fr,r,m,ins,pc) local P=fr.P r[m[ins[2]]]=r[m[ins[3]]][" +
                               vKs + "(P,ins[6])] local x=r[m[ins[2]]] if not x then r[m[ins[2]]]=P end return pc end";
        const std::string g2 = "function(fr,r,m,ins,pc) local t={} local w=0 for i=ins[3],ins[4] do w=w+1 t[w]=r[m[i]] end r[m[ins[2]]]=" +
                               vCat + "(t) return pc end";
        const std::string g3 = "function(fr,r,m,ins,pc) local P=fr.P if ins[5]>0 then r[m[ins[2]]]=#r[m[ins[3]]] else r[m[ins[2]]]=" +
                               vEnv + "[" + vKs + "(P,ins[6])] end return pc end";
        defs.push_back({913, g1});
        defs.push_back({929, g2});
        defs.push_back({947, g3});
        const std::string g4 = "function(fr,r,m,ins,pc) r[m[ins[2]]]=" + vCat + "({r[m[ins[3]]],r[m[ins[4]]]}) return pc end";
        const std::string g5 = "function(fr,r,m,ins,pc) local P=fr.P r[m[ins[2]]]=(ins[5]>0) and #r[m[ins[3]]] or " + vEnv + "[" + vKs + "(P,ins[6])] return pc end";
        const std::string g6 = "function(fr,r,m,ins,pc) local P=fr.P r[m[ins[2]]]=" + vCat + "({r[m[ins[3]]],r[m[ins[3]]]}).." + vKs + "(P,ins[6]) return pc end";
        defs.push_back({961, g4});
        defs.push_back({977, g5});
        defs.push_back({997, g6});
    }

    struct VDef { int opid; std::vector<std::string> bodies; };
    std::vector<VDef> vdefs;
    {
        auto addVariant = [&](int canon, bool withP, bool isHalt, const std::string& body) {
            int opid = b.opId[canon];
            std::vector<HDef> tmp;
            mkInto(tmp, canon, withP, isHalt, body);
            for (VDef& vd : vdefs) {
                if (vd.opid == opid) {
                    vd.bodies.push_back(tmp[0].code);
                    return;
                }
            }
            std::string base;
            for (const HDef& d : defs) {
                if (d.opid == opid) { base = d.code; break; }
            }
            vdefs.push_back({opid, {base, tmp[0].code}});
        };
        addVariant(VOP_GETGLOBAL, true, false,
           "local " + tmpN + "=" + vGnv + "(" + KI + ",fr) " + RA + "=" + tmpN);
        addVariant(VOP_GETGLOBAL, true, false,
           "local " + tmpN + "=fr.st.gm local w8=" + tmpN + " and " + tmpN + "[" + KI +
           "] or nil if w8~=nil then " + RA + "=w8[1] else " + RA + "=" + vGnv + "(" + KI + ",fr) end");
        addVariant(VOP_SETGLOBAL, true, false,
           "local " + tmpN + "=" + vSnv + "(" + KI + "," + RA + ",fr)");
        addVariant(VOP_SETT, false, false,
           "local " + tmpN + "=" + RA + " " + RB + "[" + RC + "]=" + tmpN);
        addVariant(VOP_SETT_K, true, false,
           "local " + tmpN + "=" + RA + " " + RB + "[" + KI + "]=" + tmpN);
        addVariant(VOP_SETLIST, false, false,
           "local t=" + RA + " local off=ins[4]*24-24 "
           "if ins[3]==0 then local m0=r[m[ins[2]+1]][" + vMk +
               "] local p9=ins[4] if p9>0 then p9=p9-1 else p9=#t end for i=1,m0.n do t[p9+i]=m0[i] end "
               "else for i=1,ins[3]-1 do t[off+i]=r[m[ins[2]+i]] end end");
        addVariant(VOP_CONCAT, false, false,
           "local " + tmpN + "=" + RB + " for i=ins[3]+1,ins[4] do " + tmpN +
               "=" + tmpN + "..r[m[i]] end " + RA + "=" + tmpN);
        addVariant(VOP_UNM, false, false, RA + "=-(" + RB + ")");
        addVariant(VOP_LEN, false, false, RA + "=#(" + RB + ")");
        addVariant(VOP_VARARG, false, false,
           "if ins[3]==0 then " + RA + "={[" + vMk + "]=fr.va} else for i=1,ins[3]-1 do r[m[ins[2]+i-1]]=fr.va[i] end end");
        addVariant(VOP_VARARG1, false, false,
           "local " + tmpN + "=fr.va " + RA + "=" + tmpN + "[1]");
        addVariant(VOP_SPILL, false, false,
           "local m0=" + RA + "[" + vMk +
               "] for i=1,ins[3] do r[m[ins[2]+i-1]]=m0[i] end");
        addVariant(VOP_SELF, true, false,
           "r[m[ins[2]+1]]=" + RB + " local " + tmpN + "=" + RB + " " + RA +
               "=" + tmpN + "[" + KI + "]");
        addVariant(VOP_DIVK, true, false, RA + "=" + RB + "/(P.k[ins[6]])");
        addVariant(VOP_POWK, true, false, RA + "=" + RB + "^(P.k[ins[6]])");
        addVariant(VOP_GETGF, true, false,
           "local " + tmpN + "=" + vGnv + "(" + KI + ",fr) " + RA + "=" + tmpN +
               "[" + vKs + "(P,ins[3])]");
        addVariant(VOP_SETUPVAL, false, false,
           "local c=fr.uv[ins[3]] local " + tmpN + "=" + RA +
               " if c.r then c.r[c.m[c.idx]]=" + tmpN +
               " else c.v=" + tmpN + " end");
        addVariant(VOP_CONCATK, true, false,
           "local " + tmpN + "=" + RB + " " + RA + "=" + tmpN + ".." + KI);
        addVariant(VOP_CLOSURE, true, false,
           "local vo=fr.vo if not vo then vo={} fr.vo=vo end "
           "local cp=" + vPl + "(P.kids[ins[6]],P.st) local cells={} local nu2=#cp.uv "
           "for i=1,nu2 do local ds=cp.uv[i] "
           "if ds[1]==0 then local rg=ds[2] local c0=vo[rg] "
           "if not c0 then c0={v=r[m[rg]],r=r,m=m,idx=rg} vo[rg]=c0 end "
           "cells[i]=c0 else cells[i]=fr.uv[ds[2]] end end " + RA +
           "=" + vMc + "(cp,cells)");
        addVariant(VOP_GETT, false, false,
           "local " + tmpN + "=" + RB + " " + RA + "=" + tmpN + "[" + RC + "]");
        addVariant(VOP_LEN, false, false,
           "local " + tmpN + "=" + RB + " " + RA + "=#" + tmpN);
        addVariant(VOP_NOT, false, false,
           "local " + tmpN + "=" + RB + " " + RA + "=not " + tmpN);
        addVariant(VOP_GETT_I, false, false,
           "local " + tmpN + "=" + RB + " " + RA + "=" + tmpN + "[ins[5]]");
        addVariant(VOP_GETT_K, true, false,
           "local " + tmpN + "=" + RB + " " + RA + "=" + tmpN + "[" + KI + "]");
        addVariant(VOP_ADDI, false, false,
           "local " + tmpN + "=" + RB + " " + RA + "=" + tmpN + "+ins[5]");
        addVariant(VOP_SETUPVAL, false, false,
           "local c=fr.uv[ins[3]] local " + tmpN + "=" + RA +
               " if c.r then c.r[c.m[c.idx]]=" + tmpN +
               " else c.v=" + tmpN + " end");
        addVariant(VOP_JIFF, false, false,
           "local " + tmpN + "=not " + RA + " if " + tmpN + " then " + JRinline + " end");
        addVariant(VOP_JIFT, false, false,
           "local " + tmpN + "=" + RA + " if " + tmpN + " then " + JRinline + " end");
        addVariant(VOP_MOVE, false, false,
           "do local " + tmpN + "=" + RB + " " + RA + "=" + tmpN + " end");
        addVariant(VOP_CONCAT2, false, false,
           "local " + tmpN + "=" + RB + " " + RA + "=" + tmpN + ".." + RC);
        addVariant(VOP_SELF, true, false,
           "local " + tmpN + "=" + RB + " r[m[ins[2]+1]]=" + tmpN + " " + RA + "=" + tmpN + "[" + KI + "]");
    }

    for (size_t x = defs.size() - 1; x > 0; --x) {
        size_t j = (size_t)rng.range(x + 1);
        std::swap(defs[x], defs[j]);
    }
    int gcount = 4 + (int)rng.range(3);
    std::vector<std::vector<HDef>> groups(gcount);
    for (const HDef& h : defs) groups[rng.range(gcount)].push_back(h);
    std::vector<std::string> gNames;
    for (int g = 0; g < gcount; ++g) gNames.push_back(N());
    std::vector<int> gOrder(gcount);
    for (int g = 0; g < gcount; ++g) gOrder[g] = g;
    for (int g = gcount - 1; g > 0; --g) {
        int j = (int)rng.range((std::uint64_t)(g + 1));
        std::swap(gOrder[g], gOrder[j]);
    }

    const std::string q1 = N(), q2 = N();
    std::string handlers = vDsp + "={}\n";
    for (int g : gOrder) {
        std::string block = "local " + gNames[g] + "={";
        bool first = true;
        for (const HDef& h : groups[g]) {
            if (!first) block += ",";
            first = false;
            block += "[" + std::to_string(h.opid) + "]=" + h.code;
        }
        block += "}\n";
        handlers += block;
    }
    for (int g : gOrder)
        handlers += "for " + q1 + "," + q2 + " in pairs(" + gNames[g] +
                    ") do " + vDsp + "[" + q1 + "]=" + q2 + " end " + gNames[g] + "=nil \n";
    handlers += vDs + "={} for " + q1 + "," + q2 + " in pairs(" + vDsp +
                ") do " + vDs + "[" + q1 + "]=" + q2 + " end\n";
    if (!vdefs.empty()) {
        handlers += vVar + "={}\n";
        for (const VDef& vd : vdefs) {
            handlers += vVar + "[" + std::to_string(vd.opid) + "]={";
            for (size_t vi = 0; vi < vd.bodies.size(); ++vi) {
                if (vi) handlers += ",";
                handlers += vd.bodies[vi];
            }
            handlers += "}\n";
        }
    }
    if (std::getenv("EXF_HDUMP")) {
        std::ofstream hpre("/tmp/h_pre.txt");
        hpre << handlers;
    }
    handlers = renameIdents(handlers);
    if (std::getenv("EXF_HDUMP")) {
        std::ofstream hpost("/tmp/h_post.txt");
        hpost << handlers;
    }

    {
        const std::string sd1 = N(), sd2 = N(), sd3 = N(), sd4 = N();
        const int nsh = 8 + (int)rng.range(7);
        std::string entries;
        for (int s2 = 0; s2 < nsh; ++s2) {
            const int sopid = 500 + (int)rng.range(210);
            std::string c = "function(fr,r,m,ins,pc) local P=fr.P ";
            if (rng.chance(0.35)) {
                c += trapGuard("ins[2]");
            }
            int sform = (int)rng.range(20);
            if (sform == 0)
                c += "r[m[ins[2]]]=r[m[ins[3]]]+r[m[ins[4]]]";
            else if (sform == 1)
                c += "r[m[ins[2]]]=r[m[ins[3]]][" + vKs + "(P,ins[6])]";
            else if (sform == 2)
                c += "r[m[ins[2]]]=not r[m[ins[3]]]";
            else if (sform == 3)
                c += "r[m[ins[2]]]={} local w9=r[m[ins[3]]]";
            else if (sform == 4)
                c += "r[m[ins[2]]]=#r[m[ins[3]]]";
            else if (sform == 5)
                c += "r[m[ins[2]]]=" + vEnv + "[" + vKs + "(P,ins[6])]";
            else if (sform == 6)
                c += "r[m[ins[2]]]=" + vCat + "({r[m[ins[3]]],r[m[ins[4]]]})";
            else if (sform == 7)
                c += "if r[m[ins[3]]] then r[m[ins[2]]]=r[m[ins[3]]] end";
            else if (sform == 8)
                c += "r[m[ins[2]]]=r[m[ins[3]]]*1";
            else if (sform == 9)
                c += "if r[m[ins[3]]]==nil then r[m[ins[2]]]=0 end";
            else if (sform == 10)
                c += "r[m[ins[2]]]=r[m[ins[3]]]-r[m[ins[3]]]";
            else if (sform == 11)
                c += "r[m[ins[2]]]=(" + vKs + "(P,ins[6]) or r[m[ins[3]]])";
            else if (sform == 12)
                c += "r[m[ins[2]]]=r[m[ins[3]]]+0";
            else if (sform == 13)
                c += "if r[m[ins[4]]] then r[m[ins[2]]]=r[m[ins[3]]] else r[m[ins[2]]]=nil end";
            else if (sform == 14)
                c += "r[m[ins[2]]]=" + vCat + "({r[m[ins[3]]]})";
            else if (sform == 15)
                c += "local w7=r[m[ins[3]]] r[m[ins[2]]]=w7";
            else if (sform == 16)
                c += "r[m[ins[2]]]=(function(q8) return q8 end)(r[m[ins[3]]])";
            else if (sform == 17)
                c += "r[m[ins[2]]]=r[m[ins[3]]] and true or false";
            else if (sform == 18)
                c += "r[m[ins[2]]]=" + vCat + "({r[m[ins[3]]],r[m[ins[3]]]})";
            else
                c += "r[m[ins[2]]]=(r[m[ins[3]]])";
            if (rng.chance(0.25)) {
                c += " " + trapGuard("ins[4]");
            }
            c += " return pc end";
            c = repNames(repSlots(c, opSlots[(size_t)rng.range((std::uint64_t)VOP_DECOY11 + 1)]));
            if (!entries.empty()) entries += ",";
            entries += "[" + std::to_string(sopid) + "]=" + c + " ";
        }
        std::string shadow = "local " + sd1 + "={" + entries + "} local " + sd2 + "={} ";
        shadow += "for " + sd3 + "=1,91 do " + sd2 + "[" + sd3 + "]=" + sd1 + "[" + sd3 + "] end ";
        shadow += "local " + sd4 + "=#" + sd2 + " " + sd4 + "=" + sd4 + "+" +
                  std::to_string(1 + (int)rng.range(88)) + " ";
        handlers += shadow;
        handlers = renameIdents(handlers);
    }

    double m2 = tick2();
    std::vector<std::pair<std::string, std::string>> vars;

    const std::pair<const char*, std::string> ktabs[11] = {
        {"KMA", std::to_string(g_bc.ma)}, {"KMB", std::to_string(g_bc.mb)},
        {"KMC", std::to_string(g_bc.mc)}, {"KMD", std::to_string(g_bc.md)},
        {"KME", std::to_string(g_bc.me)}, {"KM4", std::to_string(g_bc.m4)},
        {"KSA", std::to_string(g_bc.sa)}, {"KSB", std::to_string(g_bc.sb)},
        {"KSC", std::to_string(g_bc.sc)}, {"KSD", std::to_string(g_bc.sd)},
        {"KPR", std::to_string(g_bc.pr)}};
    std::string ktoks[11];
    for (int ki = 0; ki < 11; ++ki) ktoks[ki] = std::string("@") + ktabs[ki].first + "@";
    auto V = [&](const std::string& k, std::string v) {
        for (int ki = 0; ki < 11; ++ki) {
            const std::string& tok = ktoks[ki];
            const std::string& rep = ktabs[ki].second;
            size_t tp = 0;
            while ((tp = v.find(tok, tp)) != std::string::npos) {
                v.replace(tp, tok.size(), rep);
                tp += rep.size();
            }
        }
        vars.push_back({k, std::move(v)});
    };
    double v0 = tick2();
    V("VEK", std::to_string(b.veilK));
    V("VNE", std::getenv("EXF_VDBG") ? "1" : "0");
    V("DBGP", "\"\\112\\114\\105\\110\\116\"");
    V("WM", watermark);
    V("RDRS", rdrs);
    V("JK1", junkStmts(2));
    V("JK2", junkStmts(3));
    V("JK3", junkStmts(1));
    V("KMA", std::to_string(g_bc.ma));
    V("CKW", std::to_string(g_bc.ckW));
    V("CKA", std::to_string(g_bc.ckA));
    V("CMM", std::to_string(g_bc.cmM));
    V("CMM2", std::to_string(g_bc.cmM2));
    V("IVM2", std::to_string(g_bc.ivM2));
    V("SFM", std::to_string(g_bc.sfM));
    V("BSALT", std::to_string(b.blobSalt));
    V("NSF", std::to_string(b.nsf));
    V("IVUP", ivUp);
    V("KMB", std::to_string(g_bc.mb));
    V("KMC", std::to_string(g_bc.mc));
    V("KMD", std::to_string(g_bc.md));
    V("KME", std::to_string(g_bc.me));
    V("KM4", std::to_string(g_bc.m4));
    V("KSA", std::to_string(g_bc.sa));
    V("KSB", std::to_string(g_bc.sb));
    V("KSC", std::to_string(g_bc.sc));
    V("KSD", std::to_string(g_bc.sd));
    V("KPR", std::to_string(g_bc.pr));
    V("K", vK);
    V("KDEF", kdefLit);
    V("FLR", vFlr);
    V("CHR", vChr);
    V("BYT", vByt);
    V("CAT", vCat);
    V("UPK", vUpk);
    V("ENV", vEnv);
    V("MHV", vMhv);
    V("SLV", vSlv);
    V("UKV", vUkv);
    V("RB", vRb);
    V("SMP", vSm);
    V("SUB", vSub);
    V("ALN", vAlb);
    V("POOL", poolLit);
    V("B85", b85text);
    V("D8", vD8);
    V("B", vB);
    V("IZ", vIz);
    V("DM", vDm);
    V("VD", vVd);
    V("PD", vPd);
    V("PE", vPe);
    V("DS", vDs);
    V("EV", vEv);
    V("SV", vSv);
    V("WP", vWp);
    V("NC", vNc);
    V("NOP", std::to_string(VOP_COUNT));
    V("SL", spotLit);
    V("JSET", jsLit);
    V("TB85", tblB85);
    V("NB85", nmB85);
    V("AGG", std::to_string(aggVal));
    V("MX", vMx);
    V("APL", vApl);
    V("AST", vAst);
    V("FD2", vFd2);
    V("NMD", vNmd);
    V("NMS", vNms);
    V("NMA", vNma);
    V("TB", vTb);
    V("TBS", vTbs);
    V("AGGV", vAggv);
            V("FRV", vFrv);
    V("SUV", vSuv);
    V("STR", vStr);
    V("MTH", vMth);
    V("TBL", vTbl);
    V("IVM", std::to_string(g_bc.ivM));
    V("DBGP", vNma + "[3]");
    V("SN", vSn);
    V("SB", vSb);
    V("TT", vTt);
    V("TC", vTc);
    V("PS", std::to_string(probeSalt));
    V("PV", std::to_string(probeVal));
    V("XT", vXt);
    V("EF", vEf);

    V("EFC", efcLit);
    V("EFD", efdLit);
    V("IST", N());
            V("GT", vGt);
        V("AT", vAt);
    V("OT", vOt);
    V("A8", vA8);
    V("O8", vO8);
    V("ANDF", vAnd);
    V("ORF", vOrr);
    V("CKU", vCku);
    V("NSC", vNsc);
    V("Q4", vQ4);
    V("BX", vBx);
    V("LM", vLm);
    V("KX", vKx);
    V("KX2", vKx2);
    V("CHN", vChn);
    V("CK", vCk);
    V("PK", vPk);
    V("MK", vMk);
    V("EM", vEm);
    V("FM", vFm);
    V("OP", vOp);
    V("DC", vDc);
    V("D", vDsp);
    V("IV", vIv);
    V("IVV", std::to_string(iv));
    V("K31", vC31);
    V("K31B", vC31B);
    V("K31H", vC31H);
    V("K32", vC32);
    V("K24", vC24);
    V("K23", vC23);
    V("K16", vC16);
    V("E31", e31);
    V("E31B", e31b);
    V("E31H", e31h);
    V("E32", e32);
    V("E24", e24);
    V("E23", e23);
    V("E16", e16);
    V("VAR", vVar);
    V("JS", vJs);
    V("JSET", jsLit);
    V("A1", vA1);
    V("A2", vA2);
    V("A3", vA3);
    V("SC1", std::to_string(b.sc1));
    V("SC2", std::to_string(b.sc2));
    V("SC3", std::to_string(b.sc3));
    V("PR", vPr);
    V("SS", vSs);
    V("SC", vSc);
    V("LT", vLt);
    V("LTF", vLtf);
    V("CL", vCl);
    V("KS", vKs);
    V("GS", vGs);
    V("PL", vPl);
    V("MC", vMc);
    V("RT", vRt);
    V("RN", vRn);
    V("RNA", vRnA);
    V("RNB", vRnB);
    V("RNC", vRnC);
    V("BT", vBt);
    V("ROT", std::to_string(b.rotationEvery));
    V("HANDLERS", handlers);
    V("PKV", std::to_string(b.poolKey));
    V("SIDX", std::to_string(b.stringsIdx));
    V("PFQ", std::to_string(b.probeEvery));
    V("SBX", vSbx);
    V("SIX", vSix);
    V("MKSBX", vMk2);
    V("VD2", vV2);
    V("PPV", vPv);
    V("AN", vAn);
    V("CRA", vCra);
    V("JR", vJr);
    V("BL", b.bLayer ? "1" : "0");
    V("ISAB", std::getenv("EXF_NO_ISAB") ? "0" : "1");
    V("IKP", std::to_string(g_bc.ikP));
    V("IKV1", std::to_string(g_bc.ikV1));
    V("IKV2", std::to_string(g_bc.ikV2));
    V("IK4", std::to_string(g_bc.ik4));
    V("IK5", std::to_string(g_bc.ik5));
    V("IK6", std::to_string(g_bc.ik6));
    V("IKO", std::to_string(g_bc.ikO));
    V("IKB", std::to_string(g_bc.ikB));
    V("IKS", std::to_string(g_bc.ikS));
    V("FNP", fNp);
    V("FVA", fVa);
    V("FUV", fUv);
    V("FK", fK);
    V("FKS", fKs);
    V("FCO", fCo);
    V("FFL", fFl);
    V("FKD", fKid);
    V("FKE", fKe);
    V("FNR", fNr);
    V("FRB", fRb);
    V("FDM", fDm);
    V("FLD", fLd);
    V("FJT", fJt);
    V("FM0", fM0);
    V("KVM", kvm);
    V("STT", kSt);
    V("STT2", kS2);
    V("KVMR", kKvmr);
    V("KVMR2", kR2);
    V("KPS", std::to_string(b.kPS));
    V("KPK", std::to_string(b.kPK));
    V("MV", vMv);
    V("CM", vCm);
    V("VE", vXe);
        V("FVE", fVe);
    V("FVC", fVc);
    V("FRW", fRw);
    V("FLN", fLn);
    V("FOF", fOf);
    V("FCC", fCc);
    V("FLS", fLs);
    V("FLC", fLcx);
    V("FCK", fCk3);
    V("FDQ", fDq);
    V("FTP", fTp);
    V("FTN", fTn);
    V("FPH", fPh);
    V("FEP", fEp);
    V("FAFI", fafi);
    V("FAFB", fafb);
    V("FAII", faii);
    V("FW2", fW2);
    V("FW2I", fW2I);
    V("FW3", fW3);
    V("FW3I", fW3I);
    V("FW4", fW4);
    V("FW4F", fW4F);
    V("ST0", vSt0);
                                V("FKSD", fKsd);
    V("SLN", vSln);
    V("SRP", vSrp);
    V("SEL", vSel);
            V("FCM", fCm);
    V("FCE", fCe);
    V("CLSID", std::to_string(b.opId[(std::size_t)VOP_CLOSURE]));
    V("TRP", vTrp);
    V("FIB", fIb);
    V("MWLN", vMw);
    double v1 = tick2();
    if (timing2) {
        std::fprintf(stderr, "TIME5 Vcalls=%.1f\n", v1 - v0);
    }
    V("CK3", vCk3);
    V("KEP", vKep);
    V("K9", vK9);
    V("A9", vA9);
    V("LA9", vLa9);
    V("LB9", vLb9);

    std::string pinInit;
    {
        static const char* pinned[] = {
            "print", "string", "math", "table", "select", "unpack",
            "pairs", "ipairs", "next", "type", "tostring", "tonumber",
            "rawget", "rawset", "rawequal", "setmetatable", "getmetatable",
            "pcall", "xpcall", "error", "assert"
        };
        auto escName = [](const std::string& s) {
            std::string o = "\"";
            for (char ch : s) {
                o += "\\";
                o += std::to_string((unsigned char)ch);
            }
            o += "\"";
            return o;
        };
        std::unordered_set<std::string> pinnedSeen;
        pinInit = "local " + vPin + "={} do local q9=" + vEnv + " local t9=" + vPin + "\n";
        for (const char* nm : pinned) {
            std::string e = escName(nm);
            pinInit += "t9[" + e + "]=q9[" + e + "]\n";
            pinnedSeen.insert(nm);
        }
        for (const std::string& nm : b.pinNames) {
            if (pinnedSeen.count(nm)) continue;
            pinnedSeen.insert(nm);
            std::string e = escName(nm);
            pinInit += "t9[" + e + "]=q9[" + e + "]\n";
        }
        pinInit += "end\n";
    }
    V("PININI", pinInit);

    {
        std::string pkLit = "\"";
        const std::uint8_t* pkB = ed25519::publisherPubkey();
        for (int i = 0; i < 32; ++i) {
            pkLit += "\\";
            pkLit += std::to_string((unsigned)pkB[i]);
        }
        pkLit += "\"";

        if (b.sig.empty()) {
            V("SIGCHK", "");
        } else {

            std::string sg85 = b85Encode(b.sig, alpha);
            std::string gate = "local " + vSgv + "=" + vD8 + "(\"" + sg85 + "\")\n"
                               "if not " + vSgv + " or #" + vSgv + "~=64 then " + vWp + "() end\n"
                               "if not " + vE5v + "(" + vB + "," + vSgv + "," + pkLit + ") then " + vWp + "() end";
            V("SIGCHK", gate);
        }
        V("PKS", pkLit);
        V("SGV", vSgv);
        V("S512", vS512);
        V("E5V", vE5v);
        V("X8", vX8);
        V("XRF", vXrf);
        V("S5KC", ed25519::luaSha512K());
        V("S5IC", ed25519::luaSha512IV());
    }
    V("PIN", vPin);
    V("GNV", vGnv);
    V("SNV", vSnv);

    V("GWR", b.sandboxGlobals ? "" : " " + vEnv + "[nm]=val");
    V("ERR", vErr);
    V("XP", vXp);
    V("VG2", std::to_string(56 + (int)rng.range(160)));

    int vr2 = b.totalInstr / 6;
    if (vr2 < 12) vr2 = 12;
    if (vr2 > 200) vr2 = 200;
    if (std::getenv("EXF_NO_CMVER")) vr2 = 1000000;
    V("VR2", std::to_string(vr2));
    V("VR3", std::to_string(vr2 + (vr2 / 3 < 8 ? 8 : vr2 / 3)));
    V("CMK", std::to_string(b.rotationEvery >= 4096 ? 2 : 6));
    V("HOTDISP", hotdisp);
    V("HOTDISP2", hotdisp2);
    V("HOTDISP3", hotdisp3);
    V("RNS", std::to_string((int)rng.range(3)));
    if (std::getenv("EXF_HOTDBG")) {
        std::ofstream hf("/tmp/hotdisp.txt");
        hf << hotdisp;
    }

    auto minifyOut = [](const std::string& s) {
        auto idch = [](char x) {
            return (x >= 'a' && x <= 'z') || (x >= 'A' && x <= 'Z') ||
                   (x >= '0' && x <= '9') || x == '_';
        };
        std::string o;
        o.reserve(s.size());
        bool inStr = false;
        char q = 0;
        size_t i = 0;
        while (i < s.size()) {
            if (inStr) {
                size_t j = i;
                while (j < s.size()) {
                    char c = s[j];
                    if (c == '\\') {
                        j += 2;
                        continue;
                    }
                    if (c == q) {
                        ++j;
                        break;
                    }
                    ++j;
                }
                if (j > s.size()) j = s.size();
                o.append(s, i, j - i);
                i = j;
                if (i > 0 && i <= s.size() && s[i - 1] == q) inStr = false;
                continue;
            }
            char c = s[i];
            if (c == '"' || c == '\'') {
                inStr = true;
                q = c;
                o.push_back(c);
                ++i;
                continue;
            }
            if (c == '-' && i + 1 < s.size() && s[i + 1] == '-') {

                while (i < s.size() && s[i] != '\n') ++i;
                continue;
            }
            if (c == '\n') {
                size_t j = i + 1;
                while (j < s.size() && (s[j] == ' ' || s[j] == '\t')) ++j;
                char prev = o.empty() ? ' ' : o.back();
                char next = (j < s.size()) ? s[j] : ' ';
                if (idch(prev) && idch(next)) o.push_back(' ');
                i = j;
                continue;
            }
            size_t j = i;
            while (j < s.size()) {
                char d = s[j];
                if (d == '"' || d == '\'' || d == '\n') break;
                ++j;
            }
            o.append(s, i, j - i);
            i = j;
        }
        return o;
    };

    auto subst = [&](const std::string& t) {
        std::string o;
        std::unordered_map<std::string, std::string> map(vars.begin(), vars.end());
        size_t pos = 0;
        while (pos < t.size()) {
            size_t at = t.find('@', pos);
            if (at == std::string::npos) {
                o += t.substr(pos);
                break;
            }
            o += t.substr(pos, at - pos);
            size_t end = t.find('@', at + 1);
            if (end == std::string::npos) {
                o += t.substr(at);
                break;
            }
            std::string key = t.substr(at + 1, end - at - 1);
            auto it = map.find(key);
            if (it != map.end()) {
                o += it->second;
                pos = end + 1;
            } else {
                if (std::getenv("EXF_SUBDBG"))
                    std::fprintf(stderr, "SUBMISS key=%s ctx=%s\n", key.c_str(),
                                 t.substr(at > 60 ? at - 60 : 0, 100).c_str());
                o += '@';
                pos = at + 1;
            }
        }
        return o;
    };

    double e3 = tick2();
    double m4 = tick2();
    std::string out = subst(tmpl);
    {
        const std::pair<const char*, const std::string*> stab[] = {
            {"2147483647", &vC31}, {"2147483646", &vC31B},
            {"2147483648", &vC31H}, {"4294967296", &vC32},
            {"16777216", &vC24}, {"8388608", &vC23}, {"65536", &vC16}};
        auto isId = [](char x) {
            return (x >= 'a' && x <= 'z') || (x >= 'A' && x <= 'Z') ||
                   (x >= '0' && x <= '9') || x == '_';
        };
        std::string o;
        o.reserve(out.size() + out.size() / 8);

        static unsigned char scanHit[256];
        static bool scanHitInit = false;
        if (!scanHitInit) {
            for (int c2 = '0'; c2 <= '9'; ++c2) scanHit[c2] = 1;
            scanHit[(unsigned char)'"'] = 1;
            scanHit[(unsigned char)'\''] = 1;
            scanHitInit = true;
        }
        bool inStr = false;
        char q = 0;
        size_t i = 0;
        while (i < out.size()) {
            if (inStr) {
                o.push_back(out[i]);
                if (out[i] == '\\') {
                    if (i + 1 < out.size()) o.push_back(out[i + 1]);
                    i += 2;
                    continue;
                }
                if (out[i] == q) inStr = false;
                ++i;
                continue;
            }
            size_t j = i;
            while (j < out.size() && !scanHit[(unsigned char)out[j]]) ++j;
            if (j > i) {
                o.append(out, i, j - i);
                i = j;
            }
            if (i >= out.size()) break;
            char c = out[i];
            if (c == '"' || c == '\'') {
                inStr = true;
                q = c;
                o.push_back(c);
                ++i;
                continue;
            }
            if (c >= '0' && c <= '9') {
                size_t j = i;
                while (j < out.size() && out[j] >= '0' && out[j] <= '9') ++j;
                char pv = i > 0 ? out[i - 1] : 0;
                char nx = j < out.size() ? out[j] : 0;
                bool hit = false;
                if (!(pv && (isId(pv) || pv == '.')) &&
                    !(nx && (isId(nx) || nx == '.'))) {
                    std::string tok = out.substr(i, j - i);
                    for (const auto& sp : stab) {
                        if (tok == sp.first) {
                            o += *sp.second;
                            hit = true;
                            break;
                        }
                    }
                }
                if (!hit) o.append(out, i, j - i);
                i = j;
                continue;
            }
            o.push_back(c);
            ++i;
        }
        out.swap(o);
    }
    double e4 = tick2();
    if (timing2) {
        std::fprintf(stderr, "TIME2 blob85+alpha=%.1f renTmpl+handlers=%.1f preSubst=%.1f subst+num=%.1f\n",
                     e1 - e0, e2 - e1, e3 - e2, e4 - e3);
        std::fprintf(stderr, "TIME4 mkdefs->hotdisp=%.1f postToVars=%.1f tblFold=%.1f\n", m1 - e2, m2 - m1, m4 - m3);
    }
    int pick = -1;
    const char* wf = std::getenv("EXF_WRAP");
    if (wf && wf[0] >= '0' && wf[0] <= '4' && wf[1] == '\0') {
        pick = wf[0] - '0';
    } else {
        int roll = (int)rng.range(150);
        pick = roll < 60 ? 0 : roll < 120 ? 1 : roll < 130 ? 2 : roll < 140 ? 3 : 4;
    }

    std::string pre, suf;
    switch (pick) {
        case 0:
            pre = "(function(...)";
            suf = " end)(...)";
            break;
        case 1:
            pre = "return (function(...)";
            suf = " end)(...)";
            break;
        case 2:
            pre = "return (table.unpack or unpack)({true," + escStr("exfuscator") +
                  ",0x41,(function(...)";
            suf = " end)(...)})";
            break;
        case 3:
            pre = "return ({[1]=function(...)";
            suf = " end})[1](...)";
            break;
        default:
            pre = "return {[1]=(function(...)";
            suf = " end)(...)}";
            break;
    }
    int dof = 2 + (int)rng.range(2);
    std::string dop, dcl;
    for (int q = 0; q < dof; ++q) {
        dop += "do ";
        dcl += " end";
    }
    if (std::getenv("EXF_DUMP_TMPL")) {
        std::ofstream td("/tmp/tmpl_dump.lua");
        td << out;
    }
    out = pre + "\n" + dop + "\n" + out + "\n" + dcl + "\n" + suf;
    if (!std::getenv("EXF_NOTEX")) out = vmTexture(out, rng);
    if (std::getenv("EXF_DUMP_TEX")) {
        std::ofstream td("/tmp/tex_dump.lua");
        td << out;
    }
    if (std::getenv("EXF_RAWOUT")) return out;
    return minifyOut(out);
}

}
}
