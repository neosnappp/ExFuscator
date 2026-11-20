local base = 'hello v6'
local log = {}
local counters = { hits = 0, misses = 0 }

local function join(...)
  local n = select('#', ...)
  local out = ''
  for i = 1, n do
    out = out .. tostring((select(i, ...)))
  end
  return out
end

local function stamp(word, k)
  local s = string.format('%s-%s', word, string.rep('*', k))
  table.insert(log, #s)
  return s
end

local function uniq(t)
  local seen = {}
  local out = {}
  for _, v in ipairs(t) do
    if not seen[v] then seen[v] = true out[#out + 1] = v end
  end
  return out
end

local function makeAcc(seed)
  local total = seed
  return function(delta)
    total = total + delta
    if total % 2 == 0 then
      counters.hits = counters.hits + 1
    else
      counters.misses = counters.misses + 1
    end
    return total
  end
end


local function matMul(a, b)
  local rows, mid, cols = #a, #b, #b[1]
  local out = {}
  for i = 1, rows do
    out[i] = {}
    for j = 1, cols do
      local sum = 0
      for k = 1, mid do
        sum = sum + a[i][k] * b[k][j]
      end
      out[i][j] = sum
    end
  end
  return out
end

local function matShow(m)
  local out = ''
  for i = 1, #m do
    if i > 1 then out = out .. ' ' end
    out = out .. table.concat(m[i], ',')
  end
  return out
end

local function rankItems(items)
  local copy = {}
  for i, it in ipairs(items) do copy[i] = it end
  table.sort(copy, function(x, y)
    local kx = (x.w * 31 + x.id) % 100
    local ky = (y.w * 31 + y.id) % 100
    if kx == ky then return x.id < y.id end
    return kx < ky
  end)
  local keys = {}
  for i, it in ipairs(copy) do keys[i] = (it.w * 31 + it.id) % 100 end
  return keys
end

local function scrub(s)
  local cleaned = s:gsub('[%c%s]+', '_')
  local digits = 0
  for _ in s:gmatch('%d') do digits = digits + 1 end
  return cleaned, digits
end

for i = 1, 4 do
  if stamp(base, i) == 'h' then
    print 'branch found?? no way'
  elseif join('a', 'b', #log) == 'ab0' then
    print 'still no branch for u :)'
  else
    print(string.format('did u got the branchs while deobfuscating ? (v6) run=%d', i))
  end
end

local acc = makeAcc(40)
local a1 = acc(2)   -- 42
local a2 = acc(9)   -- 51
print('acc=' .. a1 .. ',' .. a2 .. ' hits=' .. counters.hits .. ' misses=' .. counters.misses)

local m1 = { { 1, 2, 3 }, { 4, 5, 6 } }
local m2 = { { 7, 8 }, { 9, 10 }, { 11, 12 } }
print('mat=' .. matShow(matMul(m1, m2)))

local keys = rankItems({
  { id = 3, w = 2 }, { id = 1, w = 2 }, { id = 7, w = 1 }, { id = 5, w = 2 },
})
print('rank=' .. table.concat(keys, ','))

local cleaned, digits = scrub('  ab\t12cd  34ef ')
print('scrub=' .. cleaned .. ' digits=' .. digits)

local mixed = uniq({ 'x', 'y', 'x', 'z', 'y', 'w' })
table.sort(log)
print('log=' .. table.concat(log, ',') .. ' uniq=' .. table.concat(mixed, '') ..
      ' join=' .. join(1, 2, 3) .. ' mask=' .. math.floor(2 ^ 23 % 1000))
