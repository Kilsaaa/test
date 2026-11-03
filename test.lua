--[[
    engine.lua - makes the action bars bigger, and everything else that changes how the bars are laid out.

    Every component in the interfaces below (and the frames two levels above them) has its width, height and place multiplied by the
    chosen percentage. The game puts things back to their own size at times (locking or unlocking the interface, and while a bar is
    dragged), so the scaled sizes are held: they are checked on every frame and set again the moment the game changes them.

    Terms
      original / base   the size and place the game gave a component (what a size of 100% means)
      target            the scaled size a held component should have
      held              a component whose target is being kept
      X                 table of internal helpers and shared state (avoids Lua's 200-local limit)
      Engine.*          public API used by other files

    See ARCHITECTURE.md for the overall design, module responsibilities, and review focus areas.
    Tuned numeric constants live in core/constants.lua.

    Bars
      interface 1430            the main action bar (statics 9, 16, 22 and 57 are the health, prayer, summoning and adrenaline bars)
      interfaces 1670 to 1673   the four additional action bars (windows 1477:74, 79, 84, 89); 1477:69 and 1477:72 to 73 hold the main bar
    Shapes: 1 = 1x14 flat, 2 = 2x7 flat, 3 = 7x2 upright, 4 = 14x1 upright. Classic mode lays everything out as 1x14 but wider.
]]

local Settings = require("core/settings")
local DragFix = require("core/dragfix")
local Perf = require("tools/meter")
local C = require("core/constants")

Perf.tally = Perf.tally or function() end      -- (an older meter.lua has no counters)
Perf.peak = Perf.peak or function() end

local Engine = {}

-- Aliases for frequently used constants (keeps call sites short and readable)
local INTERFACES = C.INTERFACES
local PARENT_LEVELS = C.PARENT_LEVELS
local MAX_STATIC_ID = C.MAX_STATIC_ID
local SMALL_OFFSET = C.SMALL_OFFSET
local FILL_SPRITES = C.FILL_SPRITES
local FILL_MAX_HEIGHT = C.FILL_MAX_HEIGHT
local FRAME_SPRITE_MIN, FRAME_SPRITE_MAX = C.FRAME_SPRITE_MIN, C.FRAME_SPRITE_MAX
local BAR_PIECE_MAX_HEIGHT = C.BAR_PIECE_MAX_HEIGHT
local READBACK_TOLERANCE = C.READBACK_TOLERANCE
local RESCAN_ALL_EVERY = C.RESCAN_ALL_EVERY
local FRAME_EVERY = C.FRAME_EVERY
local OTHERS_IDLE_EVERY = C.OTHERS_IDLE_EVERY
local QUIET_AFTER = C.QUIET_AFTER
local OTHERS_EVERY = C.OTHERS_EVERY
local BURST_FRAMES = C.BURST_FRAMES
local LOCK_VAR = C.LOCK_VAR
local FORCE_FRAMES = C.FORCE_FRAMES
local PROBE_COUNT = C.PROBE_COUNT
local QUICK_PROBES = C.QUICK_PROBES
local MAX_QUICK_PER_FRAME = C.MAX_QUICK_PER_FRAME
local MAX_QUICK_IDLE = C.MAX_QUICK_IDLE
local SWEEP_SLICE = C.SWEEP_SLICE
local QUICK_EVERY = C.QUICK_EVERY
local WATCH_EVERY = C.WATCH_EVERY
local SETTLE_CHECKS = C.SETTLE_CHECKS
local HOLD_KEY = C.HOLD_KEY
local THICK_BAR_FONT = C.THICK_BAR_FONT
local LEFT_OVERLAP = C.LEFT_OVERLAP

local function tolerance(field) return C.tolerance(field) end
local function changeTolerance(field) return C.changeTolerance(field) end

local percent = 100                  -- the size wanted (100 = normal)

-- Shared mutable state and internal helpers.
-- Lua limits a file to 200 locals; everything that does not need to be a true local lives here.
-- Engine.* is the public API used by other modules.
local X = {
    wasHidden = {},               -- interface id -> true once it has been seen hidden (0x0)
    classicStart = false,         -- the plugin started while the bars were hidden (classic combat mode)
    holdPaused = false,           -- holding is paused while the game lays the other combat mode's layout out
    layoutChangedAt = nil,        -- watch pass at which a layout change was seen
    startRescaleAt = nil,         -- watch pass at which to scale again after starting in classic mode
    recheckAt = nil,              -- watch pass at which to scale once more after a change of combat mode
    watchPass = 0,
    gameFrameWidth = {},          -- frame key -> the width the game gave it in the other layout
    layoutSaid = {},              -- interface id -> the layout (classic = true) last announced for it
    restoredScrollerLines = 0,    -- log lines printed about scrollers that were moved
}
local summoningHidden = false        -- the summoning bar is hidden and the other three player bars fill its space
local lockHidden = false              -- the lock button (1430:268) is hidden and the player bars take its space
local twoRows = false                -- the player bars are laid out two by two, in two rows, instead of in one row
local barHeight = 0                  -- thickness of the health, adrenaline, prayer and summoning bars (0 = the normal thin bar), before scaling
local sets = {}                      -- interface id -> the scaled interface
local LAYOUT_STABLE_PASSES = 2         -- watch passes the game's sizes must stay unchanged before a new layout is taken from it
local LAYOUT_WAIT_MAX = 12             -- the longest wait for that (watch passes after the change was seen; holding is let go of at 15)
local FRAME_NEAR_TARGET = 8             -- a frame given a size this near the one set here (pixels) is put back, not taken as a size of the game's own
local RECHECK_AFTER = 6               -- watch passes after a change of combat mode at which everything is scaled once more
local MIDDLE_OVERSHOOT = 6           -- pixels the middle piece of a bar runs on past where the right end begins (the right end piece is drawn over it)
local JOIN_TOLERANCE = 3             -- the pieces of a bar's frame are joined edge to edge when that changes a piece's width by no more than this
-- A bar whose fill is fitted (a custom fill image) has its fill worked out from its frame: the frame's border is FIT_RATIO of the
-- frame's height (and of the left end's width) on every side, and the fill covers everything inside it, edge to edge, at any size.
-- (6 of the 48 pixels of the frame images is a measurement of the images, not a game value.)
local FIT_RATIO = 6 / 48
local FIT_LEFT_EXTRA = 1
local FIT_RIGHT_EXTRA = 1             -- same on the right: the fill reaches this many pixels further out (it was seen 1 pixel short)
local fillFit = {}                   -- bar kind -> true
local fillGrow = {}                  -- bar kind ("health"...) -> { width, height, left }: pixels added to that bar's fill (to the right, down and left)
local kindOfPrefix                   -- "1430:9" -> "health" (defined further down)
local holding = false
local frame, burst = 0, 0
local forceFrames = 0
local quickCalls = 0
local layoutVersion = 0          -- goes up whenever the bars are laid out again or the game's pieces are swapped for new ones
local busyVersion = 0           -- like layoutVersion, but without the slots' overlay pieces the game makes again on every ability use (these must not keep the engine in its busy mode)
local structVersion = 0         -- goes up only when the whole layout is built or undone (NOT when a filling bar's piece is made again, which in combat happens about every second: the icons and borders must not search whole interfaces for that)
local afterFrameHook = nil       -- called after the checks on EntityDraw (before the interface is drawn)
local watchTicks = 0
local loadedStreak = {}
local everScaled = false         -- a size above 100% has been used this session (so 100% is held too, see Engine.setPercent)
-- frames above the bars are shared between the interfaces: scaled once, from the size they had before anything was scaled
local parentItem, parentBase = {}, {}

local function readField(component, field) return component[field] end

-- (no closure is made here: this is called thousands of times a frame, and a new function each time was a big part of the cost)
local function try(component, field)
    local ok, value = pcall(readField, component, field)
    if ok then return value end
    return nil
end
try = Perf.counted(try)

----------------------------------------------------------------
-- FONTS
-- Text has no size setting: its size is whichever font it uses. Fonts have their size in their name (MUSEO_SANS_15PT_REGULAR,
-- P12_FULL), so the fonts are grouped by name with the number taken out, and text is moved to the member of its group whose size
-- is nearest to the original size times the percentage (never smaller than it was).
----------------------------------------------------------------
local fontNameById, fontGroups, fontsIndexed = {}, {}, false
local fontLines = 0

local function indexFonts()
    if fontsIndexed then return end
    fontsIndexed = true
    pcall(function()
        for key, value in pairs(id.Font) do
            local name, number
            if type(key) == "string" and type(value) == "number" then name, number = key, value
            elseif type(key) == "number" and type(value) == "string" then name, number = value, key end
            local size = name and name:match("(%d+)")
            if size then
                fontNameById[number] = name
                local family = (name:gsub("%d+", "#", 1))
                fontGroups[family] = fontGroups[family] or {}
                table.insert(fontGroups[family], { size = tonumber(size), id = number })
            end
        end
    end)
end

-- the font to use for text that has `fontId` at `pct` percent, or nil to leave it
local function biggerFont(fontId, pct)
    indexFonts()
    local name = fontNameById[fontId]
    if not name then return nil end
    local size = tonumber(name:match("(%d+)"))
    local group = fontGroups[(name:gsub("%d+", "#", 1))]
    if not (size and group) then return nil end
    local wanted = size * pct / 100
    local best, bestSize, bestDistance
    for _, entry in ipairs(group) do
        if entry.size >= size and (not best or math.abs(entry.size - wanted) < bestDistance) then
            best, bestSize, bestDistance = entry.id, entry.size, math.abs(entry.size - wanted)
        end
    end
    if best and bestSize > size then
        if fontLines < 15 then
            fontLines = fontLines + 1
        end
        return best
    end
    return nil
end

local function keyOf(component)
    local owner, id = try(component, "interfaceID"), try(component, "staticID")
    if type(owner) == "number" and type(id) == "number" then return owner .. ":" .. id end
    return nil
end

local function setProperty(component, field, value)
    pcall(function()
        if field == "width" then component:SetWidth(value)
        elseif field == "height" then component:SetHeight(value)
        elseif field == "x" then component:SetX(value)
        elseif field == "y" then component:SetY(value)
        else component[field] = value end
    end)
end

-- centres the text of a player bar in its box (the game left-aligns it). Tried both ways a text object can be told: the AlignTo method
-- and the alignHorizontal / alignVertical fields. What it read back is printed the first time, to show whether the game took it.
local alignReported = false
local originalAlign        -- { h, v }: how the game aligns the bar text before it is centred (read the first time, put back later)
local function centreText(component)
    local centre
    pcall(function() centre = ui.AlignMode.CENTRE end)
    if centre == nil then return end
    if not originalAlign then
        local h, v = try(component, "alignHorizontal"), try(component, "alignVertical")
        if h ~= nil and h ~= centre then originalAlign = { h = h, v = v } end
    end
    local method = try(component, "AlignTo")
    if type(method) == "function" then pcall(method, component, centre, centre) end
    pcall(function() component.alignHorizontal = centre end)
    pcall(function() component.alignVertical = centre end)
    if not alignReported then
        alignReported = true
    end
end

-- puts the text back the way the game aligned it
local function uncentreText(component)
    if not originalAlign then return end
    local method = try(component, "AlignTo")
    if type(method) == "function" and originalAlign.v ~= nil then pcall(method, component, originalAlign.h, originalAlign.v) end
    pcall(function() component.alignHorizontal = originalAlign.h end)
    if originalAlign.v ~= nil then pcall(function() component.alignVertical = originalAlign.v end) end
end

local function isLoaded(interfaceID)
    local loaded = false
    pcall(function() loaded = ui.Interfaces:GetInterface(interfaceID) ~= nil end)
    return loaded
end

----------------------------------------------------------------
-- FINDING THE COMPONENTS
----------------------------------------------------------------

-- every component in the interface: the static ones, then the dynamic ones inside each. Also returned: a key for each dynamic
-- component directly under a static one (its static component, its place in the list and its sprite: the game deletes and makes
-- dynamic components again as it updates, and the keys are how the new ones are recognised), and the statics that have dynamic ones.
local function interfaceComponents(interfaceID)
    if not isLoaded(interfaceID) then return nil end
    local list, seen, keys, dynParents, staticSeen = {}, {}, {}, {}, {}
    local function add(component, isStatic)
        if not component then return end
        local prefix
        if isStatic then
            local name = keyOf(component)
            if name then
                if staticSeen[name] then return end
                staticSeen[name] = true
                if try(component, "interfaceID") == interfaceID then prefix = name end
            end
        end
        if seen[component] then return end
        seen[component] = true
        list[#list + 1] = component
        local index = 0
        pcall(function()
            component:IterateDynamicComponents(function(child)
                index = index + 1
                if prefix and not seen[child] then keys[child] = prefix .. ":" .. index .. ":" .. tostring(try(child, "spriteID")) end
                add(child, false)
            end)
        end)
        if prefix and index > 0 then dynParents[#dynParents + 1] = { prefix = prefix, component = component } end
        pcall(function() component:IterateStaticComponents(function(child) add(child, true) end) end)
    end
    for staticID = 0, MAX_STATIC_ID do
        local ok, component = pcall(function() return ui.Interfaces:GetComponent(interfaceID, staticID) end)
        if ok and component then add(component, true) end
    end
    return list, keys, dynParents
end

local function isFill(set, component, key)
    if not key then return false end
    local sprite = try(component, "spriteID")
    if type(sprite) == "number" and FILL_SPRITES[sprite] then return true end
    local base = set.trueBase and set.trueBase[component] or set.originals[component]
    local height = base and base.height
    -- (a fill given a custom image reads -1 for its sprite, so that still counts, as long as the piece is thin and not empty)
    return type(sprite) == "number" and sprite >= -1 and type(height) == "number" and height > 0 and height <= FILL_MAX_HEIGHT
end

-- the fraction a bar shows, read from the text beside it: "26%" is 0.26, "60/60" is 1, "30,000/12,095" is more than 1 (shown as full)
local function parseFraction(text)
    if type(text) ~= "string" then return nil end
    local pct = text:match("^%s*([%d%.]+)%s*%%")
    if pct then return math.max(0, math.min(1, tonumber(pct) / 100)) end
    local have, most = (text:gsub(",", "")):match("^%s*(%d+)%s*/%s*(%d+)")
    if have then
        have, most = tonumber(have), tonumber(most)
        if most == 0 then return 0 end
        return math.max(0, math.min(1, have / most))
    end
    return nil
end

----------------------------------------------------------------
-- HOLDING THE SIZES
----------------------------------------------------------------

local rescanSet
local frameHistory = {}           -- frame key -> field -> { size = true }: the sizes this plugin has set on that frame at earlier percentages
local frameLines = 0              -- how many "frame given its own size" lines have been printed
local rescanLines = 0          -- how many "piece made again" lines have been printed

-- A size set on a component can read back a pixel or two different, so what it reads right after it was set is remembered
-- (item.seen); it only counts as "changed by the game" when it reads differently from that.
-- The other combat mode's layout (classic <-> modern) shows as a frame given a width 8-60 pixels from its original (the minimise button
-- gives far more). The moment that happens the holding is paused, so that the sizes the game lays the pieces out with are not put back
-- to the old layout's before they are looked at; a few passes later they are taken as the new sizes to scale from.
-- When the other combat mode's layout comes in, the game lays the ability buttons' pieces out again, and it works their places out from
-- the size the buttons have at that moment (a piece is centred in its button, so its place is the button's size less its own, halved).
-- With the buttons held at their scaled size that gave every piece an offset (5-7 pixels, 11 for the borders) that was then taken as the
-- game's own place and scaled again, which cut the button backgrounds up on the bars that were on screen. So the moment the change is seen,
-- everything the game has not touched yet is put back to its normal size and place (the bars come back to normal size for a moment), the
-- game lays its pieces out against that, and the result is scaled a few passes later as before.
function X.unscaleUntouched()
    local count = 0
    -- (a bar hidden now is not put back, and when the layout is taken from the game a moment later it may be shown again, still at its scaled
    -- size: bars 4 and 5 coming back from classic took 579 (526 at 110%) as the game's own width and were scaled again. They are remembered,
    -- and the layout is not taken from them: their own sizes are still the ones from before, and are scaled as usual)
    X.unscaleSkipped = {}
    for interfaceID in pairs(sets) do
        if X.isHiddenBar(interfaceID) then X.unscaleSkipped[interfaceID] = true end
    end
    for interfaceID, set in pairs(sets) do
        if not X.isHiddenBar(interfaceID) then
            for _, item in ipairs(set.held) do
                local component = item.component
                if component and not item.adaptive and not item.frame and not item.frameKey and item.seen then
                    local base = set.trueBase[component] or set.originals[component]
                    if base then
                        for field, target in pairs(item.target) do
                            if field ~= "font" and type(target) == "number" and type(base[field]) == "number" then
                                local cur, ref = try(component, field), item.seen[field]
                                if type(ref) ~= "number" then ref = target end
                                if type(cur) == "number" and math.abs(cur - ref) <= changeTolerance(field) and math.abs(cur - base[field]) > changeTolerance(field) then
                                    setProperty(component, field, base[field])
                                    count = count + 1
                                end
                            end
                        end
                    end
                end
            end
        end
    end
end

-- the window and frames of bars 2 to 5 (1477:74 to 78, 79 to 83, 84 to 88, 89 to 93): their width changes with the bar's shape (72 -> 34, say), which is
-- not the other combat mode's layout coming in
function X.isExtraFrame(key)
    local number = tonumber(tostring(key or ""):match("^1477:(%d+)$"))
    return number ~= nil and number >= 74 and number <= 93
end

-- is this frame's change of width the minimise button (a shape's own narrower frame) and not the other combat mode's layout? orig is the width the
-- frame has at its normal size, cur the one it was given.
function X.isMinimiseChange(frameKey, orig, cur)
    if frameKey ~= "1477:72" and frameKey ~= "1477:73" and frameKey ~= "1477:69" then return false end
    if type(orig) ~= "number" or type(cur) ~= "number" or not X.BAR_SHAPES or not X.COLLAPSED_SHAPES then return false end
    local extra = frameKey == "1477:72" and 0 or 4
    for index, shape in ipairs(X.BAR_SHAPES) do
        local small = X.COLLAPSED_SHAPES[index]
        if small[1] ~= shape[1] and math.abs(orig - (shape[1] + extra)) <= 3 and math.abs(cur - (small[1] + extra)) <= 3 then return true end
    end
    return false
end

function X.probeLayout(set)
    if X.holdPaused or X.layoutChangedAt then return end
    for _, item in ipairs(set.held) do
        if item.frameKey and not item.adaptive and item.seen and not X.isExtraFrame(item.frameKey) then
            local cur, ref = try(item.component, "width"), item.seen.width
            local base = item.trueBase or item.base
            local orig = type(base) == "table" and base.width or nil
            if type(cur) == "number" and type(ref) == "number" and type(orig) == "number" and math.abs(cur - ref) > changeTolerance("width") then
                local d = math.abs(cur - orig)
                -- (locking or unlocking the interface gives the frame 4 more or less width, and the plugin scales that, so the width it sets is
                -- near the original at a small percentage (583 for 530 at 110%, 57 from 526). That is this plugin's own width, not another
                -- combat mode's layout, which has sizes of its own: taking it as one scaled the bars again and made them wider each time)
                local percent = tonumber(item.percent) or 100
                local ours = false
                for _, extra in ipairs({ 0, 4, -4 }) do
                    if math.abs(cur - math.floor((orig + extra) * percent / 100 + 0.5)) <= 1.5 then ours = true end
                end
                -- (the minimise button: a bar's frame is narrower by a shape's own amount (72 -> 34 on 14x1, which is inside the range below), and
                -- that is not the other combat mode's layout: taken as one, the collapsed frame was read as the bar's normal size)
                local minimise = X.isMinimiseChange(item.frameKey, orig, cur)
                if d > 8 and d < 60 and not ours and not minimise then
                    X.holdPaused, X.pausedAt, X.layoutChangedAt = true, X.watchPass or 0, X.watchPass or 0
                    pcall(X.unscaleUntouched)
                    return
                end
            end
        end
    end
end

-- the sizes the game gave the pieces while the holding was paused become the sizes scaling starts from
function X.absorbLayout()
    local count = 0
    -- the statics of the main bar's scroller and what sits in it (its position is worked out separately)
    local scrollerStatic
    do
        local ok, value = pcall(function() return id.Component["TOPLEVEL_V2_COMBAT_BAR__ACTIONBAR_SCROLLER"] end)
        value = ok and tonumber(tostring(value)) or nil
        if value and value >= 0 and value // 65536 == 1430 then scrollerStatic = value % 65536 end
    end
    local skipped = X.unscaleSkipped or {}
    X.unscaleSkipped = {}
    for interfaceID, set in pairs(sets) do
        if skipped[interfaceID] and not X.isHiddenBar(interfaceID) then
        end
        if not X.isHiddenBar(interfaceID) and not skipped[interfaceID] then
            for _, item in ipairs(set.held) do
                local component = item.component
                if component and not item.adaptive and not item.frame then
                    if item.frameKey then
                        local base = item.trueBase or item.base
                        local width = try(component, "width")
                        if type(width) == "number" and type(base) == "table" and type(base.width) == "number" then
                            local d = math.abs(width - base.width)
                            -- (a frame the game has not written to is still at the width this plugin set (579 for 526 at 110%): that is not the
                            -- game's width for the new layout. Bars 4 and 5 are not laid out by the game while they are hidden in classic, so
                            -- their frames kept the scaled width, which was taken as the game's and scaled again: about 637, wider than the rest)
                            local ours = type(item.seen) == "table" and type(item.seen.width) == "number" and math.abs(width - item.seen.width) <= changeTolerance("width")
                            if ours and d > 8 and d < 60 and (X.ownWidthLines or 0) < 20 then
                                X.ownWidthLines = (X.ownWidthLines or 0) + 1
                            end
                            X.gameFrameWidth[item.frameKey] = (d > 8 and d < 60 and not ours) and width or nil
                        end
                    else
                        local base, true_ = set.originals[component], set.trueBase[component]
                        -- (the main bar's scroller is left out: its place is worked out separately, and what the game had set there while the bar
                        -- was being laid out was not its final place)
                        local allowed = true
                        -- (the pieces inside the main bar's player bars are not taken: the game made them again and they were scaled as they
                        -- came, so what is on them now is already scaled, and the sizes they are scaled from were kept when they were made.
                        -- Taking the scaled sizes stopped the player layout from widening them to fit their bars)
                        if interfaceID == 1430 and item.key then allowed = false end
                        if allowed and interfaceID == 1430 and scrollerStatic then
                            -- (a static has no key of its own in the item: it is found by its id, as the player layout does)
                            local itemKey = item.key and tostring(item.key) or keyOf(component)
                            local static = tonumber(itemKey and tostring(itemKey):match("^1430:(%d+)"))
                            if static and static >= scrollerStatic and static <= scrollerStatic + 4 then allowed = false end
                        end
                        -- (the main bar's ability layer keeps the place it had: what the game had there while laying the bar out was 50 too low,
                        -- which put the ability buttons and the rest of the layer below the bar. Its width and height are still taken. A guess,
                        -- from the scroller, which sits at the same place in both layouts)
                        local keepY, keepX = false, false
                        if interfaceID == 1430 and not item.key then
                            local layerOk, layerValue = pcall(function() return id.Component["TOPLEVEL_V2_COMBAT_BAR__ACTIONBAR_LAYER"] end)
                            layerValue = layerOk and tonumber(tostring(layerValue)) or nil
                            if layerValue and layerValue >= 0 and layerValue // 65536 == 1430 and keyOf(component) == "1430:" .. (layerValue % 65536) then keepY = true end
                            -- (the main bar's buttons: their x is worked out with the scroller's, and what is on them now is the place the plugin
                            -- put them, which taken as the game's was scaled a second time: 756 for 630)
                            local buttonsOk, buttonsValue = pcall(function() return id.Component["TOPLEVEL_V2_COMBAT_BAR__COMBATBAR_BUTTONS"] end)
                            buttonsValue = buttonsOk and tonumber(tostring(buttonsValue)) or nil
                            if buttonsValue and buttonsValue >= 0 and buttonsValue // 65536 == 1430 and keyOf(component) == "1430:" .. (buttonsValue % 65536) then keepX = true end
                        end
                        if base and allowed then
                            for field, target in pairs(item.target) do
                                if (keepY and field == "y") or (keepX and field == "x") then
                                    -- (left as it is)
                                elseif field ~= "font" and type(target) == "number" and type(base[field]) == "number" then
                                    local cur = try(component, field)
                                    local ref = item.seen and item.seen[field]
                                    if type(ref) ~= "number" then ref = target end
                                    -- (a size of nothing is a piece the game is in the middle of making: not taken, or it would stay invisible)
                                    local empty = (field == "width" or field == "height") and type(cur) == "number" and cur <= 0 and base[field] > 0
                                    if type(cur) == "number" and not empty and math.abs(cur - ref) > changeTolerance(field) then
                                        base[field] = cur
                                        if true_ and true_ ~= base and type(true_[field]) == "number" then true_[field] = cur end
                                        count = count + 1
                                    end
                                end
                            end
                        end
                    end
                end
            end
            -- the bar's root (static 0) is as wide as the inner frame the game gave: 526 in modern, 548 in classic. The plugin had already put
            -- the root back to its own width by the time the change was seen (it kept 631, the modern width at 120%, in classic, which
            -- cut off the scroller and the buttons), so its width is taken from the frame instead.
            local frameWidth
            for _, item in ipairs(set.held) do
                if item.frameKey and not item.adaptive then
                    local w = X.gameFrameWidth[item.frameKey]
                    if type(w) == "number" and (not frameWidth or w < frameWidth) then frameWidth = w end
                end
            end
            if frameWidth then
                for _, item in ipairs(set.held) do
                    if item.component and not item.key and not item.frameKey and not item.frame and keyOf(item.component) == interfaceID .. ":0" then
                        local base, true_ = set.originals[item.component], set.trueBase[item.component]
                        if base and type(base.width) == "number" and base.width ~= frameWidth then
                            base.width = frameWidth
                            if true_ and true_ ~= base and type(true_.width) == "number" then true_.width = frameWidth end
                            count = count + 1
                        end
                    end
                end
            end
        end
    end
end

-- the bar a fill of the status bar hangs in (looked for once)
function X.turnedParent(item)
    local parent = item.turnParent
    if parent == nil then
        local number = tonumber(tostring(item.prefix):match(":(%d+)$"))
        if number then pcall(function() parent = ui.Interfaces:GetComponent(1430, number) end) end
        parent = parent or false
        item.turnParent = parent
    end
    return parent or nil
end

-- The length of a full fill in the game's own units: the game's bar, less the four it leaves. The bar as the game made it is used, not the bar as it
-- is shown (the adrenaline bar is made longer when the summoning bar is hidden, and its fill was then worked out against that and came out 40%).
function X.turnedNativeFull(item)
    -- (the four bars are the same size as the game makes them; only the adrenaline bar is made longer here, and the layout records that longer
    -- length as its own. So the prayer bar, which is never made longer, is the one measured)
    local reference = X.nativeReference
    if reference == nil then
        pcall(function() reference = ui.Interfaces:GetComponent(1430, 16) end)
        X.nativeReference = reference or false
    end
    local parent = (reference or nil) or X.turnedParent(item)
    if not parent then return nil end
    local length = try(parent, "height")
    if type(length) ~= "number" or length <= 0 then return nil end
    return length * 100 / (item.percent or percent) - 4
end

-- A fill of an upright bar keeps the thickness it was given. The game writes four when it lays the bars out on a lock; that is put right here,
-- from the thickness the fit worked out or, if that is not known, from the last thickness the fill was seen with. What was found and what the
-- write read back as is printed (a few times) so a write the game does not take shows.
function X.holdThickness(item)
    local component = item.component
    if not component then return false end
    local height = try(component, "height")
    if type(height) ~= "number" then return false end
    local wanted = item.turnFit and item.turnFit.thickness or item.goodHeight
    if height > 6 and (not item.turnFit) then item.goodHeight = height end
    if item.turnFit and math.abs(height - wanted) <= 1 then item.goodHeight = height end
    if type(wanted) ~= "number" or math.abs(height - wanted) <= 1 then return false end
    -- (a thickness of four is the game's layout: its length is in the game's units. That is noted, for whoever works the length out next, as this
    -- puts the thickness right first and the thickness is what tells it)
    pcall(function()
        local full, w = X.turnedNativeFull(item), try(component, "width")
        if full and type(w) == "number" and w <= full + 2 then item.nativeWrite = true end
    end)
    setProperty(component, "height", wanted)
    local after = try(component, "height")
    if after ~= wanted then pcall(component.SetSize, component, try(component, "width") or 0, wanted) end
    return true
end

local function checkItem(set, item)
    if set.paused then return false end
    -- A fill of a status bar drawn turned (the two vertical shapes) is left to the game once it has been scaled: what the game writes there is already
    -- in the sizes the bar has now (a fill of 82 in a bar 108 long), so scaling it again made it grow with every update, and working it out from the
    -- text beside the bar was behind the game (the fill stayed where the value had been).
    if item.adaptive and X.shapeIndex and X.shapeIndex >= 3 and item.prefix and tostring(item.prefix):find("^1430:") then
        -- (only its sideways place is kept level with the middle of the bar behind it: the game works that out from the unscaled bar and it comes out a
        -- pixel off from the scaled backing for some lengths, which showed as the fill shifting by a pixel now and then)
        -- (for a little while after the bar was laid out again - a rebuild, a drag let go - the game's own fill values are not to be trusted: they
        -- were worked out at the game's size and only change when the value does, so a health bar that does not change stayed wrong. The fill
        -- is worked out from the value for those moments.)
        local now = X.logicCount or 0
        -- (held on every check, as the flat bars are, so a lock or unlock of the window shows nothing: the value is read again every few ticks)
        do
            if (X.turnedFracAt or -100) + 6 <= now then X.turnedFracAt = now; pcall(rescanSet, set, true, false) end
            for _, field in ipairs({ "width", "y", "x" }) do
                local wanted = X.turnedFill(set, item, field)
                if wanted and item.component and try(item.component, field) ~= wanted then setProperty(item.component, field, wanted) end
            end
        end
        -- The value of the fill is kept (item.share) and the fill is drawn from it at every check, as the flat bars are drawn from the value read off their
        -- text. These bars show no text, so the value is taken from the fill itself, once, each time the game writes it: a length that is not the one this
        -- plugin left there (item.ourWidth) is the game's. In a layout the game just made (thickness four, or noted by holdThickness) the length is in the
        -- game's units, against the full length of the bar as the game makes it; otherwise it is at the size shown, against the fitted full length.
        -- What this plugin wrote is never read as a value, which is what made the fill jump about after a lock.
        if item.component then
            local w = try(item.component, "width")
            local height = try(item.component, "height")
            local native = X.turnedNativeFull(item)
            local varNumber = tonumber(tostring(item.prefix):match(":(%d+)$"))
            local fromVars = X.varShare(varNumber)
            if fromVars then
                -- (the game's own write is not read at all when the variable gives the value)
                item.share, item.nativeWrite = fromVars, nil
            elseif type(w) == "number" and (item.share == nil or w ~= item.ourWidth or item.nativeWrite) then
                local gameUnits = item.nativeWrite or (item.turnFit and type(height) == "number" and math.abs(height - item.turnFit.thickness) > 1)
                local share
                if gameUnits and native and native > 0 and w <= native + 2 then
                    share = w / native
                else
                    local parent = X.turnedParent(item)
                    local fitFull = X.shapeIndex ~= 3 and item.turnFit and item.turnFit.full or nil
                    if not fitFull and parent then
                        local length = try(parent, "height")
                        if type(length) == "number" then fitFull = length - 4 * (item.percent or percent) / 100 end
                    end
                    if fitFull then fitFull = fitFull + X.turnedMore() end
                    if fitFull and fitFull > 0 then share = (w - X.turnedLonger(item, 1)) / fitFull end
                end
                if share then item.share = math.max(0, math.min(1, share)) end
                -- (the maximum is not sent, or only at login: when it was not seen it is worked out from a fill at its shown size)
                do
                    local bar = X.VAR_BARS[varNumber]
                    if share and share > 0.15 and not gameUnits and bar and X.vars[bar.cur] and not X.vars[bar.max] then X.vars[bar.max] = math.floor(X.vars[bar.cur] / share + 0.5) end
                end
                item.nativeWrite = nil
            end
            if item.share then
                for _, field in ipairs({ "width", "y", "x" }) do
                    local wanted = X.turnedFill(set, item, field, item.share)
                    if wanted and try(item.component, field) ~= wanted then setProperty(item.component, field, wanted) end
                end
            end
            pcall(X.holdThickness, item)
        end
        local mid = set.byKey[tostring(item.prefix) .. ":2#"]
        if mid and mid.component and item.component then
            local mx, mw = try(mid.component, "x"), try(mid.component, "width")
            local fx, fw = try(item.component, "x"), try(item.component, "width")
            if type(mx) == "number" and type(mw) == "number" and type(fx) == "number" and type(fw) == "number" and fw > 0 then
                local wanted = math.floor(mx + mw / 2 - fw / 2 + X.turnedSide(item, true) + 0.5)
                if fx ~= wanted and math.abs(fx - wanted) <= 8 then setProperty(item.component, "x", wanted) end
            end
        end
        if item.component then item.ourWidth = try(item.component, "width") end
        return false
    end
    if X.holdPaused then
        -- (nothing is put back while paused, but the width the game gives each frame is still noted: the scroller rule reads it)
        if item.frameKey and not item.adaptive then
            local width = try(item.component, "width")
            if type(width) == "number" then X.gameFrameWidth[item.frameKey] = width end
        end
        return false
    end
    if item.always and set.held and not X.layoutChangedAt then X.probeLayout(set); if X.holdPaused then return false end end
    local corrected = false
    local component = item.component
    local seen = item.seen
    local yStart = item.frameKey and try(component, "y") or nil
    local xStart = item.frameKey and try(component, "x") or nil
    -- (the sizes this plugin has set on a frame are remembered: the game puts the size it last saw back while a bar is dragged, and that
    -- size is not a size of its own to be scaled again - scaling it again made the frame bigger with every new size)
    if item.frameKey and not item.home then
        local history = frameHistory[item.frameKey]
        if not history then history = { width = {}, height = {} }; frameHistory[item.frameKey] = history end
        for _, field in ipairs({ "width", "height" }) do
            local size = item.target[field]
            if type(size) == "number" and not history[field][size] then
                history[field][size] = true
                history[field].count = (history[field].count or 0) + 1
                if history[field].count > 40 then history[field] = { [size] = true, count = 1 } end
            end
        end
    end
    -- (the fill of a main status bar in classic mode: its width is the game's own once the bars are laid out. With a status bar thicker than the default
    -- this piece is not taken as a filling bar, and was put back to the width it had when it was scaled whenever the game moved it, which showed as
    -- the fill running up and being thrown back. What it reads now is taken as its target, so there is nothing to put back.)
    if X.classicMode and X.liveFills and item.target and item.target.width ~= nil and tostring(item.key):match("^1430:%d+:4:") then
        local w = try(component, "width")
        if type(w) == "number" then item.target.width = w; seen.width = w end
    end
    for field, value in pairs(item.target) do
        local current = try(component, field)
        -- (in the vertical shapes the fill of a status bar is drawn turned, and the game moves it as well as changing its width as the value changes:
        -- these are taken from the game's own numbers, scaled, and not worked out from the text beside the bar, whose lengths are for the flat bar)
        local turned = item.adaptive and X.shapeIndex and X.shapeIndex >= 3 and item.prefix and tostring(item.prefix):find("^1430:") and true or false
        local fraction = item.adaptive and not turned and field == "width" and item.fullWidth and item.prefix and set.fractions[item.prefix]
        local forced = turned and field ~= "height" and X.turnedFill(set, item, field) or nil
        if forced then
            if type(current) ~= "number" or current ~= forced then setProperty(component, field, forced) end
            item.target[field] = forced
            seen[field] = try(component, field)
        elseif fraction then
            -- a bar whose value is known from the text beside it: its width is worked out from that, whatever the game writes
            local wanted = math.floor(fraction * item.fullWidth * item.percent / 100 + 0.5)
            if item.kind == nil then item.kind = kindOfPrefix(item.prefix) or false end
            local grow = item.kind and fillGrow[item.kind]
            if grow and wanted > 0 then wanted = wanted + grow.width + grow.left end
            -- (a bar given extra width is held exactly, so that its extra pixel is not lost to the usual allowance)
            -- (exact: the game moves the fill towards its own width by two pixels at a time, and the usual allowance let it drift that far before it was put
            -- back, so the fill ran down and jumped back; it is put to the width its value gives it on every frame, so it is never seen anywhere else)
            local allowance = 0
            if X.liveFills and X.classicMode and tostring(item.prefix):find("^1430:") then allowance = math.huge end
            if type(current) == "number" and math.abs(current - wanted) > allowance then
                setProperty(component, field, wanted)
            end
        elseif type(current) == "number" and (seen[field] == nil or math.abs(current - seen[field]) > changeTolerance(field)) then
            corrected = true
            if Perf.on then
                Perf.tally("piece corrected " .. X.ticksBucket((X.logicCount or 0) - (X.lastBurstLogic or -1000)) .. " logic ticks after a burst (" .. field .. ")")
            end
            if Perf.on and item.always then Perf.tally("frame changed by game: " .. tostring(item.frameKey) .. " " .. field .. " now " .. tostring(current) .. " (we had " .. tostring(seen[field]) .. ")") end
            -- A frame the game gives a size of its own (the minimise button halves the frames the bars sit in) is left like that: only a
            -- return to its original size is put right. The size it was given is scaled by the same amount as the frame itself.
            local original = item.trueBase or item.base
            local originalValue = type(original) == "table" and original[field] or nil
            local home = item.home and item.home[field]
            -- (a width near the one set here is the game working from OUR size (locking or unlocking gives 4 more than what it finds: 583 after
            -- 579 at 110%), not its own, and is not kept as the game's width: read as 583 it made every bar look like the classic layout)
            if item.frameKey and not item.adaptive and field == "width" and type(current) == "number"
                and not (type(value) == "number" and math.abs(current - (home or value)) <= FRAME_NEAR_TARGET and math.abs(current - (type(original) == "table" and original.width or current)) > 2) then
                X.gameFrameWidth[item.frameKey] = current
            end
            if item.frameKey and not item.adaptive and type(originalValue) == "number" and originalValue > 0 and type(value) == "number"
                and (field == "width" or field == "height") then
                local earlier = frameHistory[item.frameKey] and frameHistory[item.frameKey][field]
                if math.abs(current - originalValue) <= 2 then
                    if home then value, item.target[field], item.home[field] = home, home, nil end       -- back to normal: scaled as usual
                elseif earlier and earlier[current] and current ~= (home or value) then
                    -- a size this plugin set before (at another percentage): put right as usual, not scaled again
                    if frameLines < 40 then
                        frameLines = frameLines + 1
                    end
                elseif math.abs(current - (home or value)) <= FRAME_NEAR_TARGET then
                    -- within a few pixels of the size set here: the game giving back about the size it last saw (while it changes mode, or when
                    -- a bar is dragged), not a size of its own. It is put right as usual. (Taken as its own, the frame was scaled again:
                    -- 689 wide at 130% became 897, and the frames of the hidden bars showed as big pale boxes behind the bars.)
                    if frameLines < 40 then
                        frameLines = frameLines + 1
                    end
                elseif math.abs(current - (home or value)) > changeTolerance(field) then
                    item.home = item.home or {}
                    item.home[field] = home or value
                    -- (a frame of two rows keeps the second row's height on top of the size the game gave it, which is scaled)
                    local extra = field == "height" and item.rowExtra or 0
                    value = math.floor(current * ((home or value) - extra) / originalValue + 0.5) + extra
                    -- (a minimised 14x1 bar with two columns of status bars: the game's frame holds one column, so the second column's width is added to the
                    -- scaled frame: it was 58 wide for a player info of 72)
                    if field == "width" and twoRows and X.shapeIndex == 4 and X.isMinimiseChange(item.frameKey, originalValue, current) then
                        value = math.floor(current * (tonumber(item.percent) or 100) / 100 + 0.5) + math.floor(30 * (tonumber(item.percent) or 100) / 100 + 0.5)      -- (30: ROW_EXTRA, which is declared further down)
                    end
                    if frameLines < 40 then
                        frameLines = frameLines + 1
                    end
                    item.target[field] = value
                    -- a much wider or narrower frame than at the start is the other combat mode's layout (classic <-> modern): everything
                    -- is scaled again from the game's own sizes a few passes later, since the pieces inside kept the old layout's places
                    if field == "width" and not X.isExtraFrame(item.frameKey) and math.abs(current - originalValue) > 8 and math.abs(current - originalValue) < 60 and not X.isMinimiseChange(item.frameKey, originalValue, current) then X.layoutChangedAt = X.layoutChangedAt or (X.watchPass or 0) end
                end
            end
            if item.adaptive and (field == "width" or (turned and (field == "x" or field == "y"))) then
                local rescaled = math.floor(current * item.percent / 100 + 0.5)
                if field ~= "width" and math.abs(current) <= SMALL_OFFSET then rescaled = current end
                item.target[field] = rescaled
                setProperty(component, field, rescaled)
            else
                setProperty(component, field, value)
                -- The game keeps the bottom of a frame where it was when it changes the frame's height, by moving the frame up or down by
                -- the difference between the height it finds and the height it sets. It finds the height set here (not its own), so
                -- when the size is changed here again the frame has been moved by the wrong amount: moved back by the difference.
                -- (the same for the width: the game keeps the right edge of a window where it was when the width changes, as the minimise button does, by
                -- moving it by the difference between the width it finds (the one set here) and the one it sets. The window was then given the scaled width
                -- over that, so its right edge was a little further right each time: the bar crept across the screen with every collapse and expand)
                if xStart and field == "width" and item.lastX and type(seen[field]) == "number" and type(value) == "number"
                    and xStart ~= item.lastX and math.abs((xStart - item.lastX) - (seen[field] - current)) <= 1 then
                    setProperty(component, "x", xStart - (value - current))
                end
                if yStart and field == "height" and item.lastY and type(seen[field]) == "number" and type(value) == "number"
                    and yStart ~= item.lastY and math.abs((yStart - item.lastY) - (seen[field] - current)) <= 1 then
                    setProperty(component, "y", yStart - (value - current))
                end
            end
            seen[field] = try(component, field)
        end
    end
    if yStart then item.lastY = try(component, "y") end
    if xStart then item.lastX = try(component, "x") end
    -- (centred text: the game left-aligns it again when it resets the bar, and that is not one of the sizes that are compared)
    if corrected and item.align then centreText(component) end
    return corrected
end

-- some of the held components that really changed when scaled: if the game puts them back, these show it
local sentinelsOf
local function probesOf(set)
    if set.probes then return set.probes end
    local qualifying = {}
    for _, item in ipairs(set.held) do
        if item.base and not (item.always or item.adaptive or item.frame) and #sentinelsOf(item) > 0 then
            qualifying[#qualifying + 1] = item
        end
    end
    local probes, step = {}, math.max(1, math.floor(#qualifying / PROBE_COUNT))
    for position = 1, #qualifying, step do probes[#probes + 1] = qualifying[position] end
    set.probes = probes
    return probes
end

-- the properties of a component that scaling really changed (width, height, x or y by more than a few pixels). If the game puts the
-- component back, any of these shows it: a slot's icon can have only its x put back, so one property alone is not enough.
local FIELDS = { "width", "height", "x", "y", "font" }
sentinelsOf = function(item)
    if item.sentinels then return item.sentinels end
    local list = {}
    -- (measured from the game's own sizes: a bar laid out differently (thicker, wider) has a base that already holds the new size, so
    -- at 100% nothing looked changed and the game putting things back when locked was never noticed)
    local base = item.trueBase or item.base
    if base then
        for _, field in ipairs(FIELDS) do
            local before, wanted = base[field], item.target[field]
            if type(before) == "number" and type(wanted) == "number" and math.abs(wanted - before) > changeTolerance(field) then
                list[#list + 1] = field
            end
        end
    end
    item.sentinels = list
    return list
end

-- true if the game has changed one of the properties that scaling changed
local function drifted(item, rotate)
    local fields = sentinelsOf(item)
    -- (in the slow sweep at idle one property of a piece is looked at each time, a different one on each sweep, so each is still looked at
    -- every few sweeps, for about half the reads)
    if rotate and #fields > 1 then fields = { fields[rotate % #fields + 1] } end
    for _, field in ipairs(fields) do
        local current, remembered = try(item.component, field), item.seen[field]
        if type(current) == "number" and (remembered == nil or math.abs(current - remembered) > changeTolerance(field)) then return true end
    end
    return false
end

-- the game has put things back: find the components it made again, then put right every component that has changed
local function handleHit(set)
    -- (looking at every component again is the heaviest part, so it is done at most once a frame, even while the game keeps resetting)
    if not set.lastRescan or frame - set.lastRescan >= 1 then
        set.lastRescan = frame
        pcall(rescanSet, set, true)
    end
    local fixed = 0
    for _, item in ipairs(set.held) do
        if not (item.always or item.adaptive) and drifted(item) then
            fixed = fixed + 1
            if Perf.on then Perf.tally("hit moved: " .. tostring(item.key or keyOf(item.component) or item.prefix)) end
            checkItem(set, item)
        end
    end
    Perf.tally("hits (handleHit)")
    Perf.tally("pieces found out of place in hits", fixed)
    -- (the burst of full checks on the next frames is only for a real reset by the game - a lock, a drop after a drag, a teleport - which
    -- puts many pieces out at once. A hit that finds almost nothing else wrong is the game animating one piece, as it does on every ability
    -- cast, and it was costing about 4 full sweeps a cast)
    -- (a cast moves a dozen or more slot pieces on the other bars - the cooldown shown on each bar the ability is on - so how many moved
    -- cannot tell a cast from a reset: only a forced mode, started by a lock, a frame reset or a big burst of variables, starts the burst)
    if forceFrames > 0 then
        burst = BURST_FRAMES
        Perf.tally("hits that started a burst")
    end
end

----------------------------------------------------------------
-- GAME EVENTS
----------------------------------------------------------------
local function runChecks(fastOnly)
    -- (when nothing has happened for a while the check made at the Logic event is left out: the same pieces are checked at the first
    -- EntityDraw of the frame and at Draw, before and after the interface is drawn)
    if fastOnly and frame - (X.lastBusy or 0) > QUIET_AFTER and forceFrames <= 0 and burst <= 0 then return end
    if not fastOnly then
        frame = frame + 1
        Perf.tally("frames")
        if forceFrames > 0 then Perf.tally("frames forced") end
        if burst > 0 then Perf.tally("frames in a burst") end
    end
    local forcing = forceFrames > 0
    -- (when nothing has happened for a while the sweep of everything is made less often; the small checks on every frame still catch a
    -- change at once, and these are what bring the sweep back to its normal pace)
    if not fastOnly then
        -- (a status bar's fill made again by the game is put right at once where it is found (rescanSet) and does not count as the bars being busy: in
        -- a fight it is made again about every 16 ticks, which kept every check of everything at its busiest pace, about 400 checks a tick, for as
        -- long as the fight lasted. X.FILL_REMAKE_BUSY = true brings the old behaviour back.)
        local busyNow = busyVersion - (X.FILL_REMAKE_BUSY and 0 or (X.fillRemakes or 0))
        if forcing or burst > 0 or X.holdPaused or busyNow ~= X.quietVersion then
            X.quietVersion, X.lastBusy = busyNow, frame
        end
    end
    local sweepEvery = (frame - (X.lastBusy or 0) > QUIET_AFTER) and OTHERS_IDLE_EVERY or OTHERS_EVERY
    local rotate = sweepEvery == OTHERS_IDLE_EVERY and burst <= 0 and math.floor(frame / OTHERS_IDLE_EVERY) or nil
    for _, set in pairs(sets) do
        if not fastOnly then
            -- (a piece the game made again is put right at once, with its font and position, not at the next check of everything)
            if frame % (sweepEvery == OTHERS_IDLE_EVERY and 12 or 6) == 0 then pcall(rescanSet, set, frame % RESCAN_ALL_EVERY == 0, true) end
        end
        -- the frame, the top of the interface and the filling bars are checked every time
        local reset = false
        for _, item in ipairs(set.held) do
            if (item.always or item.adaptive) and checkItem(set, item) and item.always then reset = true end
        end
        if reset then
            Perf.tally("forced by a frame reset")
            -- the game resets the frame on every tick while a bar is dragged, and letting go puts every sprite back at once
            forceFrames = math.max(forceFrames, FORCE_FRAMES)
        end
        -- after the lock variable changed (or while the frame keeps being reset), a few components are looked at on every pass,
        -- and everything is checked the moment one of them has been put back
        local everything = reset
        if forcing and not reset then
            for _, item in ipairs(set.held) do
                if not (item.always or item.adaptive) and drifted(item) then
                    everything = true
                    break
                end
            end
        end
        if everything then
            handleHit(set)
        elseif not fastOnly and (burst > 0 or frame % sweepEvery == 0) then
            local framesToo = burst > 0 or frame % FRAME_EVERY == 0
            for _, item in ipairs(set.held) do
                if not (item.always or item.adaptive) and (framesToo or not item.frame) and drifted(item, rotate) then checkItem(set, item) end
            end
        end
    end
    if not fastOnly and burst > 0 then burst = burst - 1 end
    if not fastOnly and forceFrames > 0 then forceFrames = forceFrames - 1 end
end

-- When the game rebuilds the interface (equipping an item, a teleport) it sends dozens of variables again with the SAME value, and the
-- pieces of the bars are put back to their own size for a frame. That many unchanged updates in a few frames puts the engine into its
-- forced mode. An ability cast also sends a burst, but of at most about 24 unchanged updates (measured) and the rest changed values:
-- forcing on all updates cost half the frame rate on every cast, so only the unchanged ones count, from a line above a cast's.
local VAR_BURST_FORCE = 32             -- this many unchanged updates within VAR_BURST_WINDOW frames force the look-closely mode
local VAR_BURST_WINDOW = 3             -- frames
local varBurstFrame, varBurstCount, varSameCount = -100, 0, 0

-- The name of a variable as text, remembered per variable object (building it for every event is wasted work: a busy fight sends many)
local varTexts = setmetatable({}, { __mode = "k" })
function X.varText(var)
    local kind = type(var)
    if kind == "string" then return var end
    if kind ~= "table" and kind ~= "userdata" then return tostring(var) end
    local text = varTexts[var]
    if text == nil then text = tostring(var); varTexts[var] = text end
    return text
end

-- (for the meter: how long ago, in Logic calls - about 20 ms each, 30 to a server tick - something happened, in groups of 10)
function X.ticksBucket(n)
    if n > 150 then return ">150" end
    local b = n // 10 * 10
    return b .. "-" .. (b + 9)
end

X.REBUILD_VARS = { true }          -- (set to false to switch the loadout trigger off)
local function onVar(event)
    Perf.tally("var events (onVar)")
    if event.oldValue ~= event.newValue and string.find(X.varText(event.var), LOCK_VAR, 1, true) then
        forceFrames = FORCE_FRAMES
        Perf.tally("forced by the lock variable")
    end
    -- (loading a loadout from the bank sends too few unchanged updates to reach the count below, but it sends these, and an ability cast does not)
    local name = X.varText(event.var)
    if X.REBUILD_VARS[1] and (string.find(name, "SHARE_PRESET", 1, true) or string.find(name, "WORN_SET_BASE", 1, true)) then
        if forceFrames <= 0 then Perf.tally("forced by a loadout variable") end
        forceFrames = math.max(forceFrames, FORCE_FRAMES)
    end
    if frame - varBurstFrame > VAR_BURST_WINDOW then varBurstFrame, varBurstCount, varSameCount = frame, 0, 0 end
    varBurstCount = varBurstCount + 1
    -- (an ability cast sends a burst of 12 or more: the slots are updated, and the game puts the pictures it has on them back. This does not
    -- start the forced mode - that cost half the frame rate on every cast - it only tells the borders to look at their tiles on every frame)
    if varBurstCount == 12 then
        X.slotsTouchedUntil = frame + 6
        if Perf.on then Perf.tally("burst of 12 starts " .. X.ticksBucket((X.logicCount or 0) - (X.lastBurstLogic or -1000)) .. " logic ticks after the last one") end
        X.lastBurstLogic = X.logicCount or 0
    end
    if event.oldValue == event.newValue then
        varSameCount = varSameCount + 1
        if varSameCount == VAR_BURST_FORCE then
            forceFrames = math.max(forceFrames, FORCE_FRAMES)
            Perf.tally("unchanged var bursts that forced frames")
        end
        if Perf.on then
            local c = varSameCount
            if c == 12 or c == 25 or c == 32 or c == 40 or c == 60 or c == 100 then Perf.tally("unchanged var updates reached " .. c) end
        end
    end
    if Perf.on then
        local c = varBurstCount
        if c == 12 or c == 25 or c == 40 or c == 60 or c == 100 then Perf.tally("all var updates reached " .. c) end
    end
end

-- Every ability cast resets the slot pieces of the main bar (1430:66, 79, 92 ... 13 apart: the picture of the ability or item, and the
-- cooldown piece) to the game's own size and place, at the start of the cast and again when the cooldown ends. The change log showed the
-- ordinary probes never include these, so they were put right only by the slow sweep, 1 to 14 frames late (the blink). Every piece of
-- the family is looked at on every check (before the interface is drawn and at the start of Event.Draw), so a reset is found at once.
function X.castProbes(set)
    if set.castProbes and set.castProbesFor == #set.held then return set.castProbes end
    local list = {}
    for _, item in ipairs(set.held) do
        local n = tonumber(string.match(tostring(item.key or keyOf(item.component) or ""), "^1430:(%d+)$"))
        if n and n >= 66 and (n - 66) % 13 == 0 and not (item.always or item.adaptive) and #sentinelsOf(item) > 0 then
            list[#list + 1] = item
        end
    end
    set.castProbes, set.castProbesFor = list, #set.held
    return list
end

-- true (after putting the pieces right) if the game has reset one of them. Every piece of the family is looked at, one property each (the
-- width, or the height when the width was not changed by scaling): about 15 reads
function X.castHit(set)
    local hit = false
    for _, item in ipairs(X.castProbes(set)) do
        local field = sentinelsOf(item)[1]
        local current, remembered = try(item.component, field), item.seen[field]
        if type(current) == "number" and (remembered == nil or math.abs(current - remembered) > changeTolerance(field)) then
            checkItem(set, item)
            hit = true
        end
    end
    if hit then Perf.tally("cast resets found by the cast probes") end
    return hit
end

-- Event.Draw comes after the game has drawn the frame, so a fix made there shows a frame late. EntityDraw fires many times a frame,
-- while the world is drawn (before the interface), so a very small check is made on every call.
local function quickCheck(full)
    for interfaceID, set in pairs(sets) do
        local hit = false
        if not set.alwaysList then
            -- (only these are looked at here, so they are picked out once instead of walking the whole list on every call)
            set.alwaysList = {}
            for _, item in ipairs(set.held) do
                if item.always or item.adaptive then set.alwaysList[#set.alwaysList + 1] = item end
            end
        end
        for _, item in ipairs(set.alwaysList) do
            -- the frames and the top of the interface are checked on every call: the game lays the bars out inside them when it is
            -- locked, so a frame caught at the wrong size for even one call can leave the sprites a pixel out until the next lock.
            -- The filling bars are checked on the less frequent calls.
            if item.always then
                if checkItem(set, item) then hit = true end
            elseif full and item.adaptive and checkItem(set, item) then
                hit = true
            end
        end
        -- the game makes the pieces of a bar again when a bar is dropped after being dragged, with no warning: at idle the bars' pieces
        -- are looked at once a frame, before the interface is drawn, and any the game made again are put right at once
        if forceFrames <= 0 and burst <= 0 and set.idleRescan ~= frame then
            set.idleRescan = frame
            pcall(rescanSet, set, false, true)
        end
        if not full then
            -- (nothing more on the calls in between)
        elseif forceFrames > 0 then
            -- just after a lock: every component is looked at (one property each), so none is left at the wrong size for a frame
            -- (a slice of the components on each call, moving along, so the whole list is covered over a few calls)
            -- The game makes the pieces of a bar again when it is locked, and the old ones are not the ones drawn any more, so the
            -- new ones are looked for first (once a frame). At sizes above 100% the frames being reset gave this away at once; at 100%
            -- nothing did, and the new pieces were drawn at their own size for a frame.
            if set.forceRescan ~= frame then
                set.forceRescan = frame
                pcall(rescanSet, set, true)
            end
            local held = set.held
            local count = #held
            local position = set.sweepPos or 1
            for _ = 1, math.min(SWEEP_SLICE, count) do
                if position > count then position = 1 end
                local item = held[position]
                position = position + 1
                if not (item.always or item.adaptive) and drifted(item) then
                    hit = true
                    break
                end
            end
            set.sweepPos = position
        else
            local probes = probesOf(set)
            local step = math.max(1, math.floor(#probes / QUICK_PROBES))
            for position = 1, #probes, step do
                if drifted(probes[position]) then
                    checkItem(set, probes[position])
                    hit = true
                end
            end
        end
        if interfaceID == 1430 and full and X.castHit(set) then hit = true end
        if hit then handleHit(set) end
    end
end

-- The values the bars show, read from the game's variables as they change (SA_ENERGY is adrenaline, 0 to 1000; LIFEPOINTS and MAXLIFEPOINTS are
-- health). The fills of the upright bars show no text to read a value from, so this is where it comes from. Nothing is known until a variable
-- has changed once; until then the fill's own length is used.
X.vars = {}
-- (the variable of each bar: its current value and the name its maximum is kept under. Prayer and summoning come packed, the points in the low
-- 15 bits, as the varbit mask 32767 says; their maximum is not sent, so it is worked out from the fill when that is at the size it is shown at)
X.VAR_BARS = { [9] = { cur = "life", max = "maxLife" }, [16] = { cur = "prayer", max = "maxPrayer" }, [22] = { cur = "summon", max = "maxSummon" } }
function X.noteVar(name, value)
    value = tonumber(value)
    if not value then return end
    if name:find("SA_ENERGY", 1, true) then X.vars.energy = value
    elseif name:find("MAXLIFEPOINTS", 1, true) then X.vars.maxLife = value
    elseif name:find("LIFEPOINTS", 1, true) then X.vars.life = value
    elseif name:find("PRAYER_POINTS_VAR", 1, true) then X.vars.prayer = value % 32768
    elseif name:find("LORE_POINTS_VAR", 1, true) then X.vars.summon = value % 32768 end
end

-- the share of a bar (0 to 1) from the variables, or nil when they are not known
function X.varShare(number)
    local v = X.vars
    if number == 57 then return v.energy and math.max(0, math.min(1, v.energy / 1000)) or nil end
    local bar = X.VAR_BARS[number]
    if bar and v[bar.cur] and v[bar.max] and v[bar.max] > 0 then return math.max(0, math.min(1, v[bar.cur] / v[bar.max])) end
    return nil
end

-- The values are read from the player's variables directly (var.VarPlayer.NAME.value), as the developer tutorial shows, so they are known from the
-- start and not only after a change. The events above still note them as well.
function X.readVar(name)
    local ok, value = pcall(function() return var.VarPlayer[name].value end)
    if ok and type(value) == "number" then return value end
    return nil
end

function X.refreshVars()
    local v = X.vars
    v.energy = X.readVar("SA_ENERGY") or v.energy
    v.life = X.readVar("LIFEPOINTS") or v.life
    v.maxLife = X.readVar("MAXLIFEPOINTS") or v.maxLife
    local prayer = X.readVar("PRAYER_POINTS_VAR")
    if prayer then v.prayer = prayer % 32768 end
    local summon = X.readVar("LORE_POINTS_VAR")
    if summon then v.summon = summon % 32768 end
    -- (the most prayer or summoning points a player has is the level times a hundred: 9900 at level 99, which is what the packed value reached for
    -- summoning in the log. The levels are read now and then, not every time.)
    X.levelAt = (X.levelAt or 0) + 1
    if X.levelAt % 50 == 1 then
        local function level(kind)
            local ok, value = pcall(function() return Player.GetLevelGameplay(SkillType[kind]) end)
            if ok and type(value) == "number" and value > 0 then return value end
            return nil
        end
        local prayerLevel, summoningLevel = level("PRAYER"), level("SUMMONING")
        if prayerLevel then v.maxPrayer = prayerLevel * 100 end
        if summoningLevel then v.maxSummon = summoningLevel * 100 end
    end
end

-- The dark button background behind each slot is a piece (TOPLEVEL_V2_COMBAT_BARn__BUTTON_HOLDER_BG_n) with nine dynamic children, a 3x3 grid of
-- sprites 18257 to 18265: four corners of 10x10, and edges and a middle that fill what is left of the piece's width. The children are anchored to
-- the piece's far edges, so when the piece changes size (as every rebuild of a bar does, 36 -> 47 at 130 percent) they move with it, and they were
-- left 11 further out each time: the grid was 58 wide on a 47 piece after one resize, 69 after two. They are put back to the grid that fits.
X.slotBg = {}
function X.fixSlotBackgrounds(id)
    if not isLoaded(id) then X.slotBg[id] = nil; return 0 end
    if X.classicMode and id == 1430 then return 0 end
    local cache = X.slotBg[id]
    -- (Which components are button backgrounds is fixed by the interface: the game making pieces again (structVersion changes many times a
    -- second in a fight) does not move them. Looking through all 300 components for them on every such change was the largest cost of the whole
    -- plugin, about 4,600 reads a time. They are looked for again only after a long while, or soon again when none had been found yet.)
    -- (they are looked for again after a long while all the same, and soon again if none had been found yet)
    if cache and cache.version ~= structVersion then
        local age = (X.drawCount or 0) - (cache.at or 0)
        if age < (#cache.pieces > 0 and 3600 or 120) then cache.version = structVersion end
    end
    if not cache or cache.version ~= structVersion then
        cache = { version = structVersion, at = X.drawCount or 0, pieces = {} }
        for number = 0, 300 do
            local c
            pcall(function() c = ui.Interfaces:GetComponent(id, number) end)
            if c then
                local first
                pcall(function() c:IterateDynamicComponents(function(child) if not first then first = try(child, "spriteID") end end) end)
                if first == 18257 then cache.pieces[#cache.pieces + 1] = number end
            end
        end
        X.slotBg[id] = cache
    end
    local fixed = 0
    for _, number in ipairs(cache.pieces) do
        local c
        pcall(function() c = ui.Interfaces:GetComponent(id, number) end)
        local w, h = c and try(c, "width"), c and try(c, "height")
        if c and type(w) == "number" and type(h) == "number" and w > 20 and h > 20 then
            local kids = {}
            pcall(function() c:IterateDynamicComponents(function(child) kids[#kids + 1] = child end) end)
            if #kids == 9 then
                local e = 10
                local xs, ws = { 0, e, w - e }, { e, w - 2 * e, e }
                local ys, hs = { 0, e, h - e }, { e, h - 2 * e, e }
                for index, child in ipairs(kids) do
                    local col, row = (index - 1) % 3 + 1, (index - 1) // 3 + 1
                    local want = { x = xs[col], y = ys[row], width = ws[col], height = hs[row] }
                    -- (these children are held by the scaling like every other piece: the values the hold keeps putting back are the ones it has as
                    -- targets, so they are changed there too, or the grid flickers between the two)
                    local set = sets[id]
                    local item
                    if set and set.byKey then
                        local prefix = keyOf(c)
                        if prefix then item = set.byKey[prefix .. ":" .. index .. ":" .. tostring(try(child, "spriteID"))] end
                    end
                    for field, value in pairs(want) do
                        if try(child, field) ~= value then setProperty(child, field, value); fixed = fixed + 1 end
                        if item then
                            if type(item.target) == "table" and item.target[field] ~= nil then item.target[field] = value end
                            if type(item.seen) == "table" then item.seen[field] = value end
                        end
                    end
                end
            end
        end
    end
    if fixed > 0 and (X.slotBgLines or 0) < 12 then
        X.slotBgLines = (X.slotBgLines or 0) + 1
    end
    return fixed
end

function X.slotBgTick()
    local ids = { 1430, 1670, 1671, 1672, 1673 }
    -- (right after a layout changes, every bar is looked at on every frame for a short while, so the grid is never drawn wrong for even one frame)
    -- (not on layoutVersion: that also goes up each time the game makes the slots' overlay pieces again, which it does on every ability use, and a
    -- 40-frame look at all five bars on every cast was the largest cost of the plugin in a fight: about 2,500 reads a tick)
    local layoutKey = busyVersion * 1000 + (X.otherBumps or 0)
    if X.slotBgLayout ~= layoutKey and not X.classicMode then
        X.slotBgLayout = layoutKey
        X.slotBgBurst = (X.drawCount or 0) + 40
    end
    if (X.drawCount or 0) <= (X.slotBgBurst or 0) then
        if not X.rebuilding then for _, id in ipairs(ids) do pcall(X.fixSlotBackgrounds, id) end end
        return
    end
    X.slotBgTurn = ((X.slotBgTurn or 0) % #ids) + 1
    if X.rebuilding then return end
    pcall(X.fixSlotBackgrounds, ids[X.slotBgTurn])
end

function X.drawTick()
    X.drawCount = (X.drawCount or 0) + 1
    pcall(X.extraEarly)
    -- (one bar's button backgrounds every 18th frame at rest, so each bar is looked at about every 1.5 seconds; every frame after a real layout change)
    if X.drawCount % 18 == 0 or (X.drawCount or 0) <= (X.slotBgBurst or 0) then X.slotBgTick() end
    if X.drawCount % 3 == 0 then pcall(X.classicWatch); pcall(X.extraShapeStep) end
    pcall(X.collapseInfo)      -- (on every frame: a frame that showed the bar open or closed with the abilities and status bars of the other state was seen)
    if X.drawCount - (X.lastLogicDraw or 0) >= 4 then
        X.lastLogicDraw = X.drawCount
        X.logicCount = (X.logicCount or 0) + 1
        X.logicFromDraw = (X.logicFromDraw or 0) + 1
    end
    if X.drawCount % 4 == 1 then pcall(X.refreshVars) end
end

-- With a thicker status bar the text of each bar is centred. After a change from the modern layout to the classic one the texts were left aligned
-- again (the pieces are not the ones the centring was set up for), so they are looked at here and centred when the bar has a size of its own.
function X.centreStatusText()
    if barHeight <= 0 then return end
    local centre
    pcall(function() centre = ui.AlignMode.CENTRE end)
    if centre == nil then return end
    for _, number in ipairs({ 9, 16, 22, 57 }) do
        local c
        pcall(function() c = ui.Interfaces:GetComponent(1430, number) end)
        if c then
            local index = 0
            pcall(function()
                c:IterateDynamicComponents(function(child)
                    index = index + 1
                    if index == 9 and try(child, "alignHorizontal") ~= centre then
                        centreText(child)
                    end
                end)
            end)
        end
    end
end

-- The fills of the main bar's four status bars in classic mode are set here on every frame, from the live pieces: the width is the share the
-- text beside the bar gives, of the width of the bar less the gap on both sides. After a change from the modern layout the pieces held by the
-- engine were not always the ones on screen (their full width read 90, the screen's 112) and the game's own growing of the fill showed
-- as jitter. The engine's own holding leaves these widths to this (X.liveFills).
function X.driveStatusFills()
    X.liveFills = false
    if not X.classicMode or percent <= 100 or X.holdPaused or X.layoutChangedAt or X.startRescaleAt or X.recheckAt or X.resizing or X.rebuilding then X.fillGood, X.fillSeen, X.fillInset = nil, nil, nil; return end
    if X.shapeIndex and X.shapeIndex >= 3 then return end
    X.fillGood = X.fillGood or {}
    for _, number in ipairs({ 9, 16, 22, 57 }) do
        local c
        pcall(function() c = ui.Interfaces:GetComponent(1430, number) end)
        local barWidth = c and try(c, "width")
        if type(barWidth) == "number" and barWidth > 20 then
            local fill, fraction, index = nil, nil, 0
            -- (the fill and the text beside it are found once and kept until the game makes any piece again: looking through the bar's pieces
            -- on every call, about ten times a frame, was the largest cost in classic mode)
            X.fillCache = X.fillCache or {}
            local entry = X.fillCache[number]
            if entry and entry.ver == layoutVersion and entry.c == c and entry.fill and entry.text then
                fill = entry.fill
                local content = try(entry.text, "content")
                if type(content) == "string" then fraction = parseFraction(content) end
            else
                local text
                pcall(function()
                    c:IterateDynamicComponents(function(child)
                        index = index + 1
                        if index == 4 then fill = child end
                        if fraction == nil then
                            local content = try(child, "content")
                            if type(content) == "string" then
                                fraction = parseFraction(content)
                                if fraction ~= nil then text = child end
                            end
                        end
                    end)
                end)
                if fill and text then X.fillCache[number] = { ver = layoutVersion, c = c, fill = fill, text = text } else X.fillCache[number] = nil end
            end
            local x = fill and try(fill, "x")
            if fill and fraction and type(x) == "number" then
                -- (the inset is the fill's x as it was when the bars were just laid out: a fill the game made again is at its own x, and a width worked out from that moved with it)
                X.fillInset = X.fillInset or {}
                if not (X.fillSeen and X.fillSeen[number]) or not X.fillInset[number] then X.fillInset[number] = x end
                local held = X.fillGood and X.fillGood[number]
                -- (once the fill has held one place for a second, that place is the inset: the first reading may be before the layout settled)
                if held and held.good then X.fillInset[number] = held.good.x end
                local inset = X.fillInset[number]
                local wanted = math.floor(fraction * (barWidth - 2 * inset) + 0.5)
                local grow = fillGrow[kindOfPrefix("1430:" .. number) or ""]
                if grow and wanted > 0 then wanted = wanted + grow.width + grow.left end
                -- The width of the fill is the game's own once the bars have been laid out: it moves the fill towards the new value in steps of
                -- two pixels, and sets the width from the bar it sits in, which is already the scaled one. Putting the width from the text
                -- back on every frame fought that (the fill ran down and was put back, over and over). It is set here once, when the bars
                -- have just been scaled, and left to the game after that.
                local fs = X.fillSeen and X.fillSeen[number]
                if not fs then
                    X.fillSeen = X.fillSeen or {}
                    X.fillSeen[number] = { done = true }
                    if try(fill, "width") ~= wanted then setProperty(fill, "width", wanted) end
                end
                X.liveFills = true
                -- The game makes a bar's pieces again on some events (an ability used, a prayer turned on): the new fill is at the game's own
                -- thin size for the few frames until the engine looks again, which showed as a flicker. The place and height a fill has held
                -- steady for a while are kept, and put back at once when it is given others.
                local y, h = try(fill, "y"), try(fill, "height")
                local sig = tostring(x) .. "," .. tostring(y) .. "," .. tostring(h)
                local st = X.fillGood[number]
                if not st then st = { count = 0 }; X.fillGood[number] = st end
                if st.good and sig ~= st.good.sig then
                    setProperty(fill, "x", st.good.x); setProperty(fill, "y", st.good.y); setProperty(fill, "height", st.good.h)
                    if try(fill, "width") ~= wanted then setProperty(fill, "width", wanted) end       -- (a fill made again by the game is at its own size)
                    st.obj, st.sig, st.count = fill, st.good.sig, 0
                elseif st.obj == fill and st.sig == sig then
                    st.count = st.count + 1
                    if st.count >= 60 and not st.good then st.good = { x = x, y = y, h = h, sig = sig } end
                else
                    if st.obj ~= fill then
                        -- (a fill the game made again keeps the game's own width unless it is set here: it dropped to about 40% after several abilities in a row, and sat a pixel short at 100%)
                        local now = try(fill, "width")
                        if x ~= inset then setProperty(fill, "x", inset) end
                        if type(now) == "number" and wanted > 0 and now ~= wanted then setProperty(fill, "width", wanted) end
                    end
                    st.obj, st.sig, st.count = fill, sig, 1
                end
                -- (the game also writes the fill it has, not only a new one, when an ability is used: it shifts a couple of pixels. While the value is steady
                -- the fill is put at its place and width; while the value is changing it is left to the game, which moves it in steps and fought a correction on every frame)
                local drawNow = X.drawCount or 0
                if st.lastFraction ~= fraction then st.lastFraction, st.changedAt = fraction, drawNow end
                if drawNow - (st.changedAt or 0) >= 3 and wanted > 0 then
                    local cx, cw = try(fill, "x"), try(fill, "width")
                    if (type(cx) == "number" and cx ~= inset) or (type(cw) == "number" and cw ~= wanted) then
                        if cx ~= inset then setProperty(fill, "x", inset) end
                        if cw ~= wanted then setProperty(fill, "width", wanted) end
                    end
                end
            end
        end
    end
end

local function onDraw()
    -- (the fills are driven before the interface is drawn (EntityDraw), at the end of this and at Logic; a third look at the start of every
    -- draw was not needed)
    X.drawTick()
    Perf.peak("entity calls in one frame", quickCalls)
    quickCalls = 0
    X.shapeProbe()
    -- (the game's reset of the slot pieces on a cast is put right here at once, not at the next sweep)
    if sets[1430] and X.castHit(sets[1430]) then pcall(handleHit, sets[1430]) end
    DragFix.onDraw()
    runChecks(false)
    X.holdAll()
    -- (classic: the windows of the bars sit in a stack, put right at the end of every frame: after the game reset the bar for a frame, the scaled
    -- window came back a few frames before the stack was put right, which showed as the bar jumping)
    if X.classicMode then pcall(X.restackClassic) end
    if (X.drawCount or 0) % 4 == 0 then pcall(X.centreStatusText) end
    pcall(X.driveStatusFills)
    pcall(X.repairTurned)
end

local function onLogic()
    pcall(X.driveStatusFills)
    X.logicCount = (X.logicCount or 0) + 1
    X.shapeProbe()
    X.lastLogicDraw = X.drawCount or 0
    -- (the shape the bar has is said when it changes, and is never lost: a layout that was not recognised for a moment, as when the interface is
    -- locked, left the bar with none, so it was laid out as the flat bar)
    if X.shapeIndex ~= X.shapeSaid then
        if X.shapeIndex == nil and X.shapeSaid ~= nil then X.shapeIndex = X.shapeSaid else X.shapeSaid = X.shapeIndex end
    end
    -- (while a drop is being handled the frames are left at the game's size and nothing may put them back: see dragfix.lua)
    if not DragFix.onLogic() then runChecks(true) end
    pcall(X.repairTurned)
end

-- (the game wants a boolean back from this event; true is "carry on and draw the entity as usual")
local function onEntity()
    if quickCalls == 0 then X.shapeProbe() end
    DragFix.onEntity(quickCalls == 0)
    quickCalls = quickCalls + 1
    local limit = (forceFrames > 0 or burst > 0) and MAX_QUICK_PER_FRAME or MAX_QUICK_IDLE
    if quickCalls <= limit then
        if quickCalls == 1 then X.holdAll(); pcall(X.driveStatusFills) end
        pcall(quickCheck, quickCalls == 1 or quickCalls % QUICK_EVERY == 0)
        -- (anything drawn over the bars follows them here, before the interface is drawn, not a frame late in Event.Draw)
        if afterFrameHook and (quickCalls == 1 or quickCalls % QUICK_EVERY == 0) then pcall(afterFrameHook) end
    end
    return true
end

local function updateHolding()
    local any = false
    for _, set in pairs(sets) do if #set.held > 0 then any = true end end
    if any and not holding then
        holding = pcall(function() Event.Draw.Subscribe(HOLD_KEY, Perf.wrap("engine draw", onDraw)) end)
        pcall(function() Event.Logic.Subscribe(HOLD_KEY, Perf.wrap("engine logic", onLogic)) end)
        pcall(function() Event.EntityDraw.Subscribe(HOLD_KEY, Perf.wrap("engine entity", onEntity)) end)
        pcall(function() Event.VarTransmit.Subscribe(HOLD_KEY, onVar) end)
    elseif not any and holding then
        holding = false
        pcall(function() Event.Draw.Unsubscribe(HOLD_KEY) end)
        pcall(function() Event.Logic.Unsubscribe(HOLD_KEY) end)
        pcall(function() Event.EntityDraw.Unsubscribe(HOLD_KEY) end)
        pcall(function() Event.VarTransmit.Unsubscribe(HOLD_KEY) end)
        forceFrames = 0
    end
end

----------------------------------------------------------------
-- SCALING AND RESTORING
----------------------------------------------------------------

-- remembers a component's size and position the first time it is seen
local function remember(set, component, sharedKey)
    if set.originals[component] ~= nil then return true end
    local base
    if sharedKey and parentBase[sharedKey] then
        base = parentBase[sharedKey]      -- a frame shared with another interface: its size from before anything was scaled
    else
        local width, height = try(component, "width"), try(component, "height")
        if type(width) ~= "number" or type(height) ~= "number" then return false end
        base = { width = width, height = height, x = try(component, "x"), y = try(component, "y"), font = try(component, "font") }
        if sharedKey then
            -- scaled again after the other combat mode's layout came in: the frame went back to its old layout's width when everything was
            -- put back, so the width the game gave it (kept in X.gameFrameWidth) is the one to scale from
            local gameWidth = X.layoutRescale and X.gameFrameWidth[sharedKey]
            if type(gameWidth) == "number" and math.abs(gameWidth - base.width) > 8 then
                base.width = gameWidth
            end
            parentBase[sharedKey] = base
        end
    end
    set.originals[component] = base
    set.order[#set.order + 1] = component
    -- the frames above the interface are only resized: where they sit is where the player has dragged them, so it is never restored
    if sharedKey then set.noPlace[component] = true end
    return true
end

-- sets a component to `pct` percent of the size it was remembered with; returns what it was set to (kept so it can be set again)
local function scaleOne(set, component, pct, withPosition, edgeFit)
    local base = set.originals[component]
    if not base then return nil end
    local function scaled(value) return math.floor(value * pct / 100 + 0.5) end
    local tall = set.tallBar and set.tallBar[component]      -- a part of a thicker player bar: its place is scaled like its size
    local target = { width = scaled(base.width), height = scaled(base.height) }
    -- text: a bigger font from the same family
    if withPosition and type(base.font) == "number" and base.font >= 0 and type(try(component, "content")) == "string" then
        target.font = biggerFont(base.font, pct)
        -- text in a bar made thicker uses font 83
        if set.alignText and set.alignText[component] then target.font = THICK_BAR_FONT end
    end
    if withPosition and type(base.x) == "number" and type(base.y) == "number" then
        local function place(value) if not tall and math.abs(value) <= SMALL_OFFSET then return value end return scaled(value) end
        target.x, target.y = place(base.x), place(base.y)
    end
    -- the pieces inside a bar (the backing's left, middle and right) end where the next one starts: the width is the distance between
    -- the rounded edges, not a rounded width of its own, which left a 1 pixel gap before the right end at some sizes (120%, say)
    if edgeFit and target.x and type(base.x) == "number" then
        local right = scaled(base.x + base.width)
        if right - target.x >= 1 then target.width = right - target.x end
    end
    Perf.tally("components written (scaleOne)")
    if Perf.on then Perf.tally("rewrote " .. tostring(keyOf(component) or ("dynamic " .. tostring(base.width) .. "x" .. tostring(base.height) .. " sprite " .. tostring(try(component, "spriteID"))))) end
    pcall(function() component:SetWidth(target.width); component:SetHeight(target.height) end)
    if try(component, "width") ~= target.width or try(component, "height") ~= target.height then
        Perf.tally("components written again (SetSize)")
        pcall(function() component:SetSize(target.width, target.height) end)
    end
    for field, value in pairs(target) do
        if field ~= "width" and field ~= "height" then setProperty(component, field, value) end
    end
    return target
end

-- looks again at the dynamic components under the scaled statics: one the game made again is picked up as the new version of the old one
rescanSet = function(set, everything, apply)
    if set.paused then return end      -- (the bar is being resized by its corner: nothing is looked for or scaled until it is laid out)
    for _, dp in ipairs(set.dynParents) do
        local index = 0
        local text
        if dp.fill or everything then pcall(function()
            dp.component:IterateDynamicComponents(function(child)
                index = index + 1
                if dp.fill and text == nil then
                    local content = try(child, "content")
                    if type(content) == "string" and content ~= "" then dp.lastText = content end
                    if type(content) == "string" and parseFraction(content) ~= nil then text = content end
                end
                local key = dp.prefix .. ":" .. index .. ":" .. tostring(try(child, "spriteID"))
                local item = set.byKey[key]
                -- (a bar's own pieces are also found by their place in the bar: a piece with a custom image reads sprite -1 where the game's own
                -- reads its sprite number, so after the game made the pieces again the key above could be for the other one, and the bar was left unscaled)
                if not item and dp.fill and index <= 7 then item = set.byKey[dp.prefix .. ":" .. index .. "#"] end
                -- only a component that was scaled before is picked up again; new ones are left alone (scaling one twice makes it huge)
                if item then
                    local changed = item.component ~= child
                    if changed and dp.fill and (rescanLines or 0) < 20 then
                        rescanLines = (rescanLines or 0) + 1
                    end
                    -- (the size the game made it at is kept: when the layout is worked out again, the piece must start from this, not from
                    -- the old mode's sizes it was scaled from, or the player layout's widening rules do not recognise it)
                    if changed then
                        item.remadeRaw = { x = try(child, "x"), y = try(child, "y"), width = try(child, "width"), height = try(child, "height") }
                    end
                    item.component = child
                    if changed then
                        layoutVersion = layoutVersion + 1
                        if dp.fill then busyVersion = busyVersion + 1; X.fillRemakes = (X.fillRemakes or 0) + 1 end
                        -- (not counted in structVersion: the slots' overlay pieces are made again by the game on every ability use)
                        Perf.tally(dp.fill and "pieces made again (bars)" or "pieces made again (other)")
                    end
                    if changed and item.align then centreText(child) end
                    -- (a piece the game made again is at its own size: put right at once, not on the next check)
                    if changed and apply then checkItem(set, item) end
                end
            end)
        end) end
        if dp.fill and text ~= nil then set.fractions[dp.prefix] = parseFraction(text) end
    end
end

-- puts everything in one scaled interface back to its original size and position
local function restoreSet(set)
    pcall(rescanSet, set, true)
    for _, component in ipairs(set.order) do
        local base = set.trueBase[component] or set.originals[component]
        if base then
            pcall(function() component:SetWidth(base.width); component:SetHeight(base.height) end)
            if try(component, "width") ~= base.width or try(component, "height") ~= base.height then
                pcall(function() component:SetSize(base.width, base.height) end)
            end
            if type(base.x) == "number" and type(base.y) == "number" and not set.noPlace[component] then
                pcall(function() component:SetX(base.x); component:SetY(base.y) end)
            end
            if type(base.font) == "number" and try(component, "font") ~= base.font then setProperty(component, "font", base.font) end
        end
    end
    -- text that was centred goes back to the game's own alignment
    for component in pairs(set.alignText) do uncentreText(component) end
    for _, item in ipairs(set.held) do
        if item.align and item.component then uncentreText(item.component); item.align = nil end
    end
    -- then the components that are shown now. A bar that fills gets the width its value gives it (from the text beside it), not the
    -- width it had when it was scaled, which may be a different value by now (that left the bars empty).
    for _, item in ipairs(set.held) do
        local base, component = item.trueBase or item.base, item.component
        local raw = item.remadeRaw
        item.remadeRaw = nil
        if raw and X.layoutRescale and type(raw.width) == "number" and type(raw.height) == "number" and raw.width > 0 then
            -- (a piece the game made again in the new layout goes back to the size the game gave it)
            base = { x = raw.x, y = raw.y, width = raw.width, height = raw.height, font = base and base.font }
        else
            raw = nil
        end
        if base and component then
            local width = base.width
            local fraction = not raw and item.adaptive and item.fullWidth and item.prefix and set.fractions[item.prefix]
            if fraction then width = math.floor(fraction * (item.fullWidth - (item.layoutShrink or 0)) + 0.5) end
            pcall(function() component:SetWidth(width); component:SetHeight(base.height) end)
            if type(base.x) == "number" and type(base.y) == "number" and not item.owner then
                pcall(function() component:SetX(base.x); component:SetY(base.y) end)
            end
            if type(base.font) == "number" and try(component, "font") ~= base.font then setProperty(component, "font", base.font) end
        end
    end
end

-- forgets a scaled interface without touching the game (its components are gone, or are being restored)
local function forgetSet(interfaceID)
    local set = sets[interfaceID]
    if not set then return end
    for key, item in pairs(parentItem) do
        if item.owner == interfaceID then parentItem[key] = nil end
    end
    sets[interfaceID] = nil
    updateHolding()
end

local function restoreInterface(interfaceID)
    local set = sets[interfaceID]
    if not set then return end
    forgetSet(interfaceID)
    restoreSet(set)
end

local function restoreAll()
    layoutVersion = layoutVersion + 1
    structVersion = structVersion + 1
    busyVersion = busyVersion + 1
    Perf.tally("structure changes (restoreAll)")
    local ids = {}
    for id in pairs(sets) do ids[#ids + 1] = id end
    for _, id in ipairs(ids) do restoreInterface(id) end
    parentItem = {}
    -- the frames above the bars are put back too, including any whose interface went away while they were scaled (their set was
    -- forgotten without being restored), found again by their interface and static id. Only their size is restored, not where they are.
    for key, base in pairs(parentBase) do
        local owner, id = key:match("^(%d+):(%d+)$")
        if owner then
            local ok, component = pcall(function() return ui.Interfaces:GetComponent(tonumber(owner), tonumber(id)) end)
            if ok and component then
                pcall(function() component:SetWidth(base.width); component:SetHeight(base.height) end)
                if try(component, "width") ~= base.width or try(component, "height") ~= base.height then
                    pcall(function() component:SetSize(base.width, base.height) end)
                end
            end
        end
    end
    parentBase = {}
end

-- HIDING SUMMONING: the row of player bars (health, adrenaline, prayer, summoning) is four equal sections. With summoning hidden the
-- other three become three equal sections: each container is wider, the bar inside it is wider by the same amount, and so are the
-- pieces inside the bar (the text, the middle of the backing, the filling bar; the right end of the backing moves right). This changes
-- the sizes the scaling starts from (set.originals); the true ones are kept in set.trueBase so everything can still be put back.
local PLAYER_PREFIX = "TOPLEVEL_V2_COMBAT_BAR__"
local PLAYER_SLOTS = { "PLAYER_HEALTH", "PLAYER_ADRENALINE", "PLAYER_PRAYER" }    -- left to right
local PLAYER_INFO = "COMBAT_BAR_PLAYER_INFO"

local function staticOf(name, interfaceID)
    local ok, value = pcall(function() return id.Component[PLAYER_PREFIX .. name] end)
    value = ok and tonumber(tostring(value)) or nil
    if value and value >= 0 and value // 65536 == interfaceID then return value % 65536 end
    return nil
end

local BAR_KIND_NAMES = { health = "PLAYER_HEALTH_BAR", prayer = "PLAYER_PRAYER_BAR", adrenaline = "PLAYER_ADRENALINE_BAR", summoning = "PLAYER_SUMMONING_BAR" }
local kindCache = {}
kindOfPrefix = function(prefix)
    if not prefix then return nil end
    local known = kindCache[prefix]
    if known then return known end
    for kind, name in pairs(BAR_KIND_NAMES) do
        local number = staticOf(name, 1430)
        if number and ("1430:" .. number) == prefix then kindCache[prefix] = kind; return kind end
    end
    return nil
end

----------------------------------------------------------------
-- PLAYER BARS
----------------------------------------------------------------
local PLAYER_SLOTS_ALL = { "PLAYER_HEALTH", "PLAYER_ADRENALINE", "PLAYER_PRAYER", "PLAYER_SUMMONING" }    -- left to right

local ROW_EXTRA = 30       -- height of one row of player bars (before scaling): what a second row adds to the bar

-- the player bars that are shown, left to right (and in two rows, top to bottom, when the bars are laid out two by two)
-- (in two rows the order is health, prayer on the top row and adrenaline, summoning on the bottom row)
local TWO_ROW_SLOTS = { "PLAYER_HEALTH", "PLAYER_PRAYER", "PLAYER_ADRENALINE", "PLAYER_SUMMONING" }
local TWO_ROW_SLOTS_NO_SUMMONING = { "PLAYER_HEALTH", "PLAYER_PRAYER", "PLAYER_ADRENALINE" }

local function visibleSlots()
    if twoRows then return summoningHidden and TWO_ROW_SLOTS_NO_SUMMONING or TWO_ROW_SLOTS end
    if summoningHidden then return PLAYER_SLOTS end
    return PLAYER_SLOTS_ALL
end

local function applyPlayerLayout(set, components, keys, interfaceID)
    if interfaceID == 1430 and (X.shapeIndex or 1) ~= 1 then return X.applyShapeLayout(set, components, keys, interfaceID, X.shapeIndex) end
    if not (summoningHidden or twoRows or lockHidden) and barHeight <= 0 then return end
    local visible = visibleSlots()
    local positions = {}
    for position, name in ipairs(visible) do positions[name] = position end
    local byStatic = {}
    for _, component in ipairs(components) do
        local name = keyOf(component)
        if name and not keys[component] then byStatic[name] = component end
    end
    local function baseOf(name, number) local c = number and byStatic[interfaceID .. ":" .. number]; return c, c and set.originals[c] end
    local section, fullWidth
    if twoRows or #visible < #PLAYER_SLOTS_ALL or lockHidden then
        local _, infoBase = baseOf(PLAYER_INFO, staticOf(PLAYER_INFO, interfaceID))
        if not infoBase or type(infoBase.width) ~= "number" then return end
        fullWidth = infoBase.width
        section = math.floor(infoBase.width / (twoRows and 2 or #visible) + 0.5)
    end
    local function change(component, changes)
        local before = set.originals[component]
        set.trueBase[component] = set.trueBase[component] or before
        local after = {}
        for field, value in pairs(before) do after[field] = value end
        for field, value in pairs(changes) do after[field] = value end
        set.originals[component] = after
    end
    for index, name in ipairs(PLAYER_SLOTS_ALL) do
        local containerNumber, barNumber = staticOf(name, interfaceID), staticOf(name .. "_BAR", interfaceID)
        local container, containerBase = baseOf(name, containerNumber)
        local bar, barBase = baseOf(name .. "_BAR", barNumber)
        if container and containerBase and bar and barBase then
            -- wider: the bars that are shown share the row (or, in two rows, each takes half of it)
            local delta = 0
            if section and positions[name] and section > containerBase.width then
                local position = positions[name] - 1
                -- (the edges are worked out from the whole length, so that the bars meet exactly when it does not divide evenly)
                local count = twoRows and 2 or #visible
                local function edge(i) return math.floor(i * fullWidth / count + 0.5) end
                local column = twoRows and position % 2 or position
                local width = edge(column + 1) - edge(column)
                local left = edge(column)
                -- a bar alone on the bottom row (an odd number of bars) takes the whole row
                if twoRows and positions[name] == #visible and position % 2 == 0 then width = fullWidth; left = 0 end
                delta = width - containerBase.width
                if twoRows then
                    change(container, { width = width, x = left, y = containerBase.y + math.floor(position / 2) * ROW_EXTRA })
                else
                    change(container, { width = width, x = left })
                end
                change(bar, { width = barBase.width + delta })
            end
            -- thicker: the backing, the filling bar and the text sit in the middle of the bar, and the text is centred on the backing
            local thick = barHeight > 0 and type(barBase.height) == "number"
            local stripY = thick and math.floor((barBase.height - barHeight) / 2 + 0.5) or 0
            local barPrefix = interfaceID .. ":" .. barNumber
            for _, component in ipairs(components) do
                local key = keys[component]
                local base = key and set.originals[component]
                if base and key:match("^(%d+:%d+):") == barPrefix and type(base.x) == "number" and type(base.y) == "number" and type(base.width) == "number" then
                    local oldWidth = barBase.width
                    local changes, tall = {}, false
                    if delta > 0 then
                        if base.width == oldWidth then changes.width = base.width + delta                                    -- the text
                        elseif base.x == 16 and base.width == oldWidth - 32 then changes.width = base.width + delta          -- middle of the backing
                        elseif base.x == oldWidth - 16 and base.width == 16 then changes.x = base.x + delta                  -- right end
                        elseif base.x == 2 and base.height == 4 then                                                          -- the filling bar
                            changes.width = math.floor(base.width * (oldWidth - 4 + delta) / (oldWidth - 4) + 0.5)
                            set.fillShrink[component] = delta
                        end
                    end
                    if thick then
                        if base.y == 16 and base.height == 8 and base.width > 0 then                                          -- the backing
                            changes.y, changes.height, tall = stripY, barHeight, true
                        elseif base.x == 2 and base.height == 4 then                                                          -- the filling bar
                            changes.y, changes.height, tall = stripY + 2, math.max(1, barHeight - 4), true
                        elseif base.height == 16 and base.width == oldWidth and base.y == 0 then                              -- the text
                            changes.y, tall = math.floor((barBase.height - base.height) / 2 + 0.5), true
                            set.alignText[component] = true
                        end
                    end
                    if next(changes) then change(component, changes) end
                    if tall then set.tallBar[component] = true end
                end
            end
        end
    end
end

-- TWO ROWS: the player info holds two rows of bars, so it is twice as tall, the bar's layer and its scroller sit one row lower, and the bar's
-- root and the two frames above it are one row taller. These are added to the scaled sizes (not to the sizes they start from), so the
-- background frame pieces, which grow with the component they sit in, grow by it.
local function applyTwoRowTargets(set, components, keys, toHold, pct, interfaceID)
    if interfaceID == 1430 and X.shapeIndex == 4 then return X.applyColumnTargets(set, components, keys, toHold, pct, interfaceID) end
    if not twoRows or (interfaceID == 1430 and (X.shapeIndex or 1) ~= 1) then return end
    local extra = math.floor(ROW_EXTRA * pct / 100 + 0.5)
    local heldBy, heldByKey = {}, {}
    for _, item in ipairs(toHold) do
        heldBy[item.component] = item
        local name = keyOf(item.component)
        if name and not keys[item.component] then heldByKey[name] = item end
    end
    local byStatic = {}
    for _, component in ipairs(components) do
        local name = keyOf(component)
        if name and not keys[component] then byStatic[name] = component end
    end
    local function itemOf(name)
        local number = staticOf(name, interfaceID)
        local component = number and byStatic[interfaceID .. ":" .. number]
        return component and heldBy[component]
    end
    local function add(item, field, amount)
        if not item or type(item.target[field]) ~= "number" then return end
        item.target[field] = item.target[field] + amount
        if field == "height" then item.rowExtra = (item.rowExtra or 0) + amount end      -- (the second row's share, not scaled with the frame)
        setProperty(item.component, field, item.target[field])
    end
    local info = itemOf(PLAYER_INFO)
    if not info then return end
    add(info, "height", extra)
    add(itemOf("ACTIONBAR_LAYER"), "y", extra)
    add(itemOf("ACTIONBAR_SCROLLER"), "y", extra)
    -- the padlock sits in the middle of the bottom row of status bars (y 28 at 100%), and the frame it sits in is one row taller
    local padlock = itemOf("FULLSCREEN_PADLOCK_LAYER")
    if padlock and type(padlock.target.y) == "number" then
        padlock.target.y = math.floor(28 * pct / 100 + 0.5)
        setProperty(padlock.component, "y", padlock.target.y)
        local parent = try(padlock.component, "parentStatic")
        local name = parent and keyOf(parent)
        local parentHeld = parent and (heldBy[parent] or (name and heldByKey[name]) or (name and parentItem[name]))
        if parentHeld and not parentHeld.twoRowsAdded then parentHeld.twoRowsAdded = true; add(parentHeld, "height", extra) end
    end
    -- the bar's root and the frames above it
    local current, level = try(info.component, "parentStatic"), 0
    while current and level < PARENT_LEVELS + 1 do
        -- (the game gives a different object each time a static is reached, so they are found by their id)
        local name = keyOf(current)
        local item = heldBy[current] or (name and heldByKey[name]) or (name and parentItem[name])
        if item and not item.twoRowsAdded then item.twoRowsAdded = true; add(item, "height", extra) end
        current = try(current, "parentStatic")
        level = level + 1
    end
end


-- THE PLAYER BARS IN THE OTHER THREE SHAPES (2x7 flat, 2x7 upright, 1x14 upright). Where the game puts each bar's holder in each shape, at size 100
-- (x, y), and how long it is. The bars hold their length along the long side: width in the flat shape, height in the upright ones.
X.SHAPE_CELLS = {
    [2] = { dim = "width",  cell = 122, thick = 30, info = 244, pos = { PLAYER_HEALTH = { 0, 0 },  PLAYER_ADRENALINE = { 122, 0 },  PLAYER_PRAYER = { 0, 24 },  PLAYER_SUMMONING = { 122, 24 } } },
    [3] = { dim = "height", cell = 114, thick = 30, info = 228, pos = { PLAYER_HEALTH = { 0, 0 },  PLAYER_ADRENALINE = { 0, 114 },  PLAYER_PRAYER = { 24, 0 },  PLAYER_SUMMONING = { 24, 114 } } },
    [4] = { dim = "height", cell = 122, thick = 30, info = 488, pos = { PLAYER_HEALTH = { 0, 0 },  PLAYER_ADRENALINE = { 0, 122 },  PLAYER_PRAYER = { 0, 244 },  PLAYER_SUMMONING = { 0, 366 } } },
}

-- where each bar goes (x, y, length) when summoning is hidden and/or the bars are in two columns; nothing when they stay as the game has them
function X.shapeTargets(shape, hidden, columns)
    if shape == 2 and hidden then
        -- adrenaline and prayer swap places, and adrenaline takes the whole of the bottom row that summoning left
        return { PLAYER_HEALTH = { 0, 0, 122 }, PLAYER_PRAYER = { 122, 0, 122 }, PLAYER_ADRENALINE = { 0, 24, 244 } }
    elseif shape == 3 and hidden then
        return { PLAYER_HEALTH = { 0, 0, 114 }, PLAYER_PRAYER = { 0, 114, 114 }, PLAYER_ADRENALINE = { 24, 0, 228 } }
    elseif shape == 4 then
        if columns then
            local list = { PLAYER_HEALTH = { 0, 0, 244 }, PLAYER_PRAYER = { 0, 244, 244 }, PLAYER_ADRENALINE = { ROW_EXTRA, 0, hidden and 488 or 244 } }
            if not hidden then list.PLAYER_SUMMONING = { ROW_EXTRA, 244, 244 } end
            return list
        elseif hidden then
            return { PLAYER_HEALTH = { 0, 0, 163 }, PLAYER_ADRENALINE = { 0, 163, 163 }, PLAYER_PRAYER = { 0, 326, 162 } }
        end
    end
    return nil
end

-- THE LOCK BUTTON HIDDEN: the player bars take the space it leaves. The length they share (the player info) is longer by this much, at the end of the
-- bar where the button was (the same strip the action bar layer takes when the two icons are hidden).
function X.lockExtra()
    if not lockHidden then return 0 end
    if X.classicMode then return 30 end
    return (X.shapeIndex or 1) == 1 and 21 or 18
end

-- the player info is made longer, in the sizes the bars are laid out from
function X.applyLockExtent(set, components, keys, interfaceID)
    local extra = X.lockExtra()
    if interfaceID ~= 1430 or extra <= 0 then return end
    local number = staticOf(PLAYER_INFO, interfaceID)
    if not number then return end
    for _, component in ipairs(components) do
        if keyOf(component) == interfaceID .. ":" .. number and not keys[component] then
            local before = set.originals[component]
            if before then
                set.trueBase[component] = set.trueBase[component] or before
                local after = {}
                for field, value in pairs(before) do after[field] = value end
                local shape = X.classicMode and 1 or (X.shapeIndex or 1)
                if shape == 3 or shape == 4 then
                    after.y, after.height = before.y - extra, before.height + extra
                else
                    after.width = before.width + extra
                end
                set.originals[component] = after
            end
            return
        end
    end
end

-- where each bar goes (x, y, length) over a length L, in the shapes other than the 1x14 flat one
function X.lockTargets(shape, hidden, columns, L)
    local function edge(i, n) return math.floor(i * L / n + 0.5) end
    local function span(i, n) return edge(i, n), edge(i + 1, n) - edge(i, n) end
    local a, la = span(0, 2)
    local b, lb = span(1, 2)
    if shape == 2 then
        if hidden then return { PLAYER_HEALTH = { 0, 0, la }, PLAYER_PRAYER = { b, 0, lb }, PLAYER_ADRENALINE = { 0, 24, L } } end
        return { PLAYER_HEALTH = { 0, 0, la }, PLAYER_ADRENALINE = { b, 0, lb }, PLAYER_PRAYER = { 0, 24, la }, PLAYER_SUMMONING = { b, 24, lb } }
    elseif shape == 3 then
        if hidden then return { PLAYER_HEALTH = { 0, a, la }, PLAYER_PRAYER = { 0, b, lb }, PLAYER_ADRENALINE = { 24, 0, L } } end
        return { PLAYER_HEALTH = { 0, a, la }, PLAYER_ADRENALINE = { 0, b, lb }, PLAYER_PRAYER = { 24, a, la }, PLAYER_SUMMONING = { 24, b, lb } }
    elseif shape == 4 then
        if columns then
            local list = { PLAYER_HEALTH = { 0, a, la }, PLAYER_PRAYER = { 0, b, lb }, PLAYER_ADRENALINE = { ROW_EXTRA, 0, hidden and L or la } }
            if not hidden then list.PLAYER_SUMMONING = { ROW_EXTRA, b, lb } end
            return list
        end
        local n = hidden and 3 or 4
        local order = hidden and { "PLAYER_HEALTH", "PLAYER_ADRENALINE", "PLAYER_PRAYER" } or { "PLAYER_HEALTH", "PLAYER_ADRENALINE", "PLAYER_PRAYER", "PLAYER_SUMMONING" }
        local list = {}
        for i, name in ipairs(order) do
            local at, length = span(i - 1, n)
            list[name] = { 0, at, length }
        end
        return list
    end
    return nil
end

function X.applyShapeLayout(set, components, keys, interfaceID, shape)
    local cells = X.SHAPE_CELLS[shape]
    if not cells then return end
    local targets = X.shapeTargets(shape, summoningHidden, twoRows and shape == 4) or {}
    if X.lockExtra() > 0 then targets = X.lockTargets(shape, summoningHidden, twoRows and shape == 4, cells.info + X.lockExtra()) end
    if next(targets) == nil and barHeight <= 0 and shape ~= 3 then return end
    local byStatic = {}
    for _, component in ipairs(components) do
        local name = keyOf(component)
        if name and not keys[component] then byStatic[name] = component end
    end
    local function baseOf(name, number) local c = number and byStatic[interfaceID .. ":" .. number]; return c, c and set.originals[c] end
    local function change(component, changes)
        local before = set.originals[component]
        set.trueBase[component] = set.trueBase[component] or before
        local after = {}
        for field, value in pairs(before) do after[field] = value end
        for field, value in pairs(changes) do after[field] = value end
        set.originals[component] = after
    end
    local dim = cells.dim
    local upright = dim == "height"
    for _, name in ipairs(PLAYER_SLOTS_ALL) do
        local target = targets[name]
        local container, containerBase = baseOf(name, staticOf(name, interfaceID))
        local bar, barBase = baseOf(name .. "_BAR", staticOf(name .. "_BAR", interfaceID))
        if container and containerBase and bar and barBase and type(containerBase[dim]) == "number" and type(barBase[dim]) == "number" then
            local delta = target and (target[3] - containerBase[dim]) or 0
            if target then change(container, { x = target[1], y = target[2], [dim] = target[3] }) end
            do
                local oldLength = barBase[dim]
                if delta ~= 0 then change(bar, { [dim] = oldLength + delta }) end
                -- (1x14 upright: the bar's own box, which cuts off what hangs outside it, is two pixels (on screen) taller at the top, and what is in
                -- it is put two pixels further down so that nothing moves)
                local lift = 0
                if shape == 4 and type(set.originals[bar].y) == "number" and type(set.originals[bar].height) == "number" then
                    lift = 2 * 100 / math.max(1, percent)
                    change(bar, { y = set.originals[bar].y - lift, height = set.originals[bar].height + lift })
                    -- (adrenaline with summoning hidden: its backing and fill reach further down than the game's box, which cuts them off: the box is
                    -- made four pixels (on screen) taller at the bottom, more than they reach so that nothing is cut)
                    if summoningHidden and name == "PLAYER_ADRENALINE" then
                        change(bar, { height = set.originals[bar].height + 4 * 100 / math.max(1, percent) })
                    end
                end
                -- (7x2: the bar's own box, which cuts off what hangs outside it, a pixel wider on screen)
                local barPrefix = interfaceID .. ":" .. staticOf(name .. "_BAR", interfaceID)
                local thick = barHeight > 0
                -- (7x2: the bar's own box, which cuts off what hangs outside it, a pixel wider on screen, to the left. What is in it is put a pixel to the
                -- right of where it was in it, so that nothing moves.)
                if shape == 3 and type(set.originals[bar].width) == "number" and type(set.originals[bar].x) == "number" then
                    local d = 1   -- (a pixel at 100%, in the units the bar is scaled from, so that it grows with the scale)
                    -- (at status bar size 20 and over, two pixels at each side instead)
                    local big = barHeight >= 20
                    local left, right = big and 2 * d or d, big and 2 * d or 0
                    change(bar, { x = set.originals[bar].x - left, width = set.originals[bar].width + left + right })
                    -- (and at status bar size 20 and over a pixel taller on screen at the top and at the bottom, with what is in it moved down by that pixel)
                    local e = (barHeight >= 20 and type(set.originals[bar].y) == "number" and type(set.originals[bar].height) == "number") and 2 * d or 0
                    if e ~= 0 then change(bar, { y = set.originals[bar].y - e, height = set.originals[bar].height + 2 * e }) end
                    for _, component in ipairs(components) do
                        local key = keys[component]
                        local base = key and set.originals[component]
                        if base and key:match("^(%d+:%d+):") == barPrefix and type(base.x) == "number" then
                            local index = tonumber(key:match("^%d+:%d+:(%d+):"))
                            local down = (big and index and index ~= 4 and index ~= 8 and index ~= 9) and d or 0   -- (the backing a pixel lower at size 20 and over)
                            change(component, { x = base.x + left, y = type(base.y) == "number" and base.y + e + down or base.y })
                        end
                    end
                end
                X.flatBackY = nil
                for _, component in ipairs(components) do
                    local key = keys[component]
                    local base = key and set.originals[component]
                    if base and key:match("^(%d+:%d+):") == barPrefix and key:match("^%d+:%d+:(%d+):") == "2" and type(base.y) == "number" then X.flatBackY = base.y end
                end
                for _, component in ipairs(components) do
                    local key = keys[component]
                    local base = key and set.originals[component]
                    if base and key:match("^(%d+:%d+):") == barPrefix and type(base.x) == "number" and type(base.y) == "number"
                        and type(base.width) == "number" and type(base.height) == "number" then
                        local index = tonumber(key:match("^%d+:%d+:(%d+):"))
                        local changes, tall
                        if delta == 0 then
                            changes = nil
                        elseif upright then
                            -- (drawn turned: the pieces' width is along the bar; ends top and bottom, the middle in the middle, the fill hangs from the top)
                            local half = math.floor(delta / 2 + 0.5)
                            if index == 3 or index == 7 then changes = { y = base.y + delta }
                            elseif index == 2 or index == 6 then changes = { width = base.width + delta, y = base.y + half, x = base.x - half }
                            elseif index == 4 then
                                local width = math.floor(base.width * (oldLength - 4 + delta) / (oldLength - 4) + 0.5)
                                changes = { width = width, y = math.floor(width / 2 + 0.5), x = math.floor(barBase.width / 2 + 4 - width / 2 + 0.5) }
                            end
                        else
                            if base.width == oldLength then changes = { width = base.width + delta }                                    -- the text
                            elseif base.x == 16 and base.width == oldLength - 32 then changes = { width = base.width + delta }          -- middle of the backing
                            elseif base.x == oldLength - 16 and base.width == 16 then changes = { x = base.x + delta }                  -- right end
                            elseif base.x == 2 and base.height == 4 then                                                                -- the filling bar
                                changes = { width = math.floor(base.width * (oldLength - 4 + delta) / (oldLength - 4) + 0.5) }
                                set.fillShrink[component] = delta
                            end
                        end
                        -- thicker. Flat (2x7): as in the 1x14 bar, the backing, the filling bar and the text sit in the middle of the bar and the text is
                        -- centred on the backing. Upright: the pieces are drawn turned, so their height is the thickness of the bar and it grows around
                        -- the middle of the piece (the text stays at the top, as wide as the bar).
                        if shape == 3 then
                            -- (the backing, both its layers, a pixel further left; the fill three taller, which is wider on screen, to the left)
                            changes = changes or {}
                            if base.height == 8 and index ~= 8 and index ~= 9 then changes.x = (changes.x or base.x) - 2
                            elseif index == 4 and base.height == 4 then changes.height = (thick and math.max(1, barHeight - 4) or base.height) + 2 end
                        end
                        if thick then
                            changes = changes or {}
                            if upright then
                                local shift = math.floor((8 - barHeight) / 2 + 0.5)
                                if base.height == 8 and index ~= 8 and index ~= 9 then
                                    changes.height, changes.y = barHeight, (changes.y or base.y) + shift
                                elseif index == 4 and base.height == 4 then
                                    changes.height, changes.y = math.max(1, barHeight - 4) + (shape == 3 and 2 or 0), (changes.y or base.y) + shift
                                end
                            else
                                -- (the game's flat bar here has its backing low (y 19 in a bar 26 high, its bottom cut off by the bar's own edge): a thicker
                                -- backing, the fill inside it and the text are put in the middle of the bar's height, as in the 1x14 bar)
                                local stripY = math.floor((barBase.height - barHeight) / 2 + 0.5)
                                if base.height == 8 and index ~= 8 and index ~= 9 and base.width > 0 then
                                    changes.y, changes.height, tall = stripY, barHeight, true
                                elseif index == 4 and base.height == 4 then
                                    changes.y, changes.height, tall = stripY + 2, math.max(1, barHeight - 4), true
                                elseif index == 9 and base.width == oldLength then
                                    changes.y, tall = math.floor((barBase.height - base.height) / 2 + 0.5), true
                                    set.alignText[component] = true
                                end
                            end
                        end
                        if lift ~= 0 then changes = changes or {}; changes.y = (changes.y or base.y) + lift end
                        if changes and next(changes) then change(component, changes) end
                        if tall then set.tallBar[component] = true end
                    end
                end
            end
        end
    end
end

-- Two columns (the 1x14 upright shape): the second column makes the bar wider by one column, as a second row makes the flat bar taller. The player
-- info, the bar's root and the frames above it are wider by it.
function X.applyColumnTargets(set, components, keys, toHold, pct, interfaceID)
    if not twoRows then return end
    local extra = math.floor(ROW_EXTRA * pct / 100 + 0.5)
    local heldBy, heldByKey, byStatic = {}, {}, {}
    for _, item in ipairs(toHold) do
        heldBy[item.component] = item
        local name = keyOf(item.component)
        if name and not keys[item.component] then heldByKey[name] = item end
    end
    for _, component in ipairs(components) do
        local name = keyOf(component)
        if name and not keys[component] then byStatic[name] = component end
    end
    local function itemOf(name)
        local number = staticOf(name, interfaceID)
        local component = number and byStatic[interfaceID .. ":" .. number]
        return component and heldBy[component]
    end
    local function add(item, amount)
        if not item or type(item.target.width) ~= "number" then return end
        item.target.width = item.target.width + amount
        setProperty(item.component, "width", item.target.width)
    end
    local info = itemOf(PLAYER_INFO)
    if not info then return end
    add(info, extra)
    local current, level = try(info.component, "parentStatic"), 0
    while current and level < PARENT_LEVELS + 1 do
        local name = keyOf(current)
        local item = heldBy[current] or (name and heldByKey[name]) or (name and parentItem[name])
        if item and not item.twoRowsAdded then item.twoRowsAdded = true; add(item, extra) end
        current = try(current, "parentStatic")
        level = level + 1
    end
end

-- which of the four shapes the main bar has now (from the frame the bar sits in), or nothing
function X.shapeNow()
    local frame
    pcall(function() frame = ui.Interfaces:GetComponent(1477, 72) end)
    local width, height = frame and try(frame, "width"), frame and try(frame, "height")
    if type(width) ~= "number" or type(height) ~= "number" then return nil end
    return X.shapeIndexOf(width, height)
end

function Engine.twoRowsAllowed() local shape = X.shapeIndex or 1; return shape == 1 or shape == 4 end

-- The three pieces of each turned bar's backing (two layers of them): where their lengths and thicknesses go together so that every edge falls on
-- a whole pixel (a box turned about its middle has whole-pixel edges only when its length and thickness are both odd or both even; the 1x14 upright
-- shape had ends and middle a pixel apart in thickness without this), all with the same middle across the bar, and meeting end to end.
function X.fixTurnedBacking(toHold, byKey, interfaceID, early)
    if not (X.shapeIndex and X.shapeIndex >= 3 and interfaceID == 1430) then return end
    -- (the 1x14 upright shape is done before the fill is fitted to it; the 2x7 upright one after, as it was tuned)
    if (X.shapeIndex == 4) ~= (early == true) then return end
    local prefixes = {}
    for _, item in ipairs(toHold) do
        if item.prefix and tostring(item.prefix):find("^1430:") then prefixes[item.prefix] = true end
    end
    local function numbers(item)
        local t = item and item.target
        if t and type(t.x) == "number" and type(t.y) == "number" and type(t.height) == "number" and type(t.width) == "number" then return t end
    end
    for prefix in pairs(prefixes) do
        for _, layer in ipairs({ { 1, 2, 3 }, { 5, 6, 7 } }) do
            local first, middle, last = byKey[prefix .. ":" .. layer[1] .. "#"], byKey[prefix .. ":" .. layer[2] .. "#"], byKey[prefix .. ":" .. layer[3] .. "#"]
            local f, m, l = numbers(first), numbers(middle), numbers(last)
            if f and m and l and m.width > 0 and first.component and last.component then
                local shiftLeft, overlap = 0, 0
                if X.shapeIndex == 4 then
                    -- (the whole backing a pixel left and a pixel up)
                    m.y = m.y - 1; setProperty(middle.component, "y", m.y); middle.seen.y = try(middle.component, "y")
                    local across = m.x + m.width / 2
                    -- (adrenaline with summoning hidden: its backing is a pixel further up and two longer at the bottom: a pixel more at each end)
                    if summoningHidden and kindOfPrefix(prefix) == "adrenaline" then
                        m.width = m.width + 2; setProperty(middle.component, "width", m.width); middle.seen.width = try(middle.component, "width")
                        -- (and then a pixel further left, and a pixel further down: the middle two longer with its top where it was, the last end
                        -- reaching under it by a pixel so that it is a pixel further down)
                        shiftLeft, overlap = 1, 0
                    end
                    for _, piece in ipairs({ first, middle, last }) do
                        local t = piece.target
                        if (t.width + t.height) % 2 ~= 0 then t.width = t.width + 1; setProperty(piece.component, "width", t.width); piece.seen.width = try(piece.component, "width") end
                        local x = math.floor(across - t.width / 2 + 0.5) - 1 - shiftLeft
                        if t.x ~= x then t.x = x; setProperty(piece.component, "x", x); piece.seen.x = try(piece.component, "x") end
                    end
                end
                if X.shapeIndex == 3 then
                    -- (7x2: the two ends of the backing a pixel to the left (a pixel at 100%, in step with the scale), once each. The middle is then put on the
                    -- middle of the two ends, as the 1x14 upright shape puts all three on one line, so that however each piece was rounded they stay in line
                    -- at every scale. The fill follows the middle.)
                    for _, piece in ipairs({ first, last }) do
                        if not piece.shiftedLeft then
                            piece.shiftedLeft = true
                            local t = piece.target
                            t.x = t.x - math.max(1, math.floor(percent / 100 + 0.5)); setProperty(piece.component, "x", t.x); piece.seen.x = try(piece.component, "x")
                        end
                    end
                    -- (each piece is turned about its middle: its edges fall on whole pixels only when its width and height are both even or both odd, so
                    -- a piece that is not is made a pixel longer, as the 1x14 upright shape does, and not half a pixel off the others)
                    for _, piece in ipairs({ first, middle, last }) do
                        local t = piece.target
                        if (t.width + t.height) % 2 ~= 0 then t.width = t.width + 1; setProperty(piece.component, "width", t.width); piece.seen.width = try(piece.component, "width") end
                    end
                    local across = math.floor((f.x + f.width / 2 + l.x + l.width / 2) / 2 + 0.5)
                    local x = math.floor(across - m.width / 2 + 0.5) - (X.tweak7x2().mid or 0)
                    if m.x ~= x then m.x = x; setProperty(middle.component, "x", x); middle.seen.x = try(middle.component, "x") end
                end
                local centre = m.y + m.height / 2
                local top, bottom = centre - m.width / 2, centre + m.width / 2
                local firstY = math.floor(top - f.width / 2 - f.height / 2 + X.SEAM + 0.5)
                local lastY = math.floor(bottom + l.width / 2 - l.height / 2 - X.SEAM - overlap + 0.5)
                if f.y ~= firstY then f.y = firstY; setProperty(first.component, "y", firstY); first.seen.y = try(first.component, "y") end
                if l.y ~= lastY then l.y = lastY; setProperty(last.component, "y", lastY); last.seen.y = try(last.component, "y") end
            end
        end
    end
end

-- scales one interface to `pct` percent (from its true original sizes). Returns false if it isn't loaded.
-- After a change from the modern layout to the classic one the game lays the pieces inside each status bar (backing, fill, text box) out to the
-- width of the bar as it was when it was scaled, while the bar itself is put back to its own size first. The pieces were then taken as the
-- original sizes and scaled a second time (a text box of 139 inside a bar of 116: too wide, clipping, and a fill that was worked out from the
-- wrong width). Here the widths and positions of the pieces are put back in proportion with their bar, so they are taken as a classic start takes them.
function X.normaliseStatusChildren()
    -- The pieces of a status bar as the classic layout makes them (before any scaling): a backing of three pieces (an end of 16 on each side and the
    -- middle between them, at x 0, 16 and the bar's width less 16) and a box for the text as wide as the bar. After a change from the modern layout
    -- the pieces come back at the modern bar's sizes, or at the sizes of the bar as it was scaled; the widening of the bars (two rows, summoning
    -- hidden) and the scaling work from these sizes and need the classic ones, as when the client starts in classic.
    local END = 16
    for _, number in ipairs({ 9, 16, 22, 57 }) do
        local c
        pcall(function() c = ui.Interfaces:GetComponent(1430, number) end)
        local barWidth = c and try(c, "width")
        if type(barWidth) == "number" and barWidth > 2 * END + 4 then
            local children, index = {}, 0
            pcall(function() c:IterateDynamicComponents(function(child) index = index + 1; children[index] = child end) end)
            local changed = false
            local function put(child, x, width, y, height)
                if not child then return end
                if try(child, "x") ~= x then setProperty(child, "x", x); changed = true end
                if try(child, "width") ~= width then setProperty(child, "width", width); changed = true end
                if y and try(child, "y") ~= y then setProperty(child, "y", y); changed = true end
                if height and try(child, "height") ~= height then setProperty(child, "height", height); changed = true end
            end
            -- (the heights and places too: the layout recognises the backing (8 high at 16), the fill (4 high at 18, 2 in) and the text box (16 high)
            -- by them, and a fill that came back at the modern bar's thickness was not taken as a fill at all - the bar's own images were never put on
            -- it, and it was held to the width it had when it was scaled)
            for _, first in ipairs({ 1, 5 }) do
                put(children[first], 0, END, 16, 8)
                put(children[first + 1], END, barWidth - 2 * END, 16, 8)
                put(children[first + 2], barWidth - END, END, 16, 8)
            end
            if children[4] and try(children[4], "x") ~= 2 then setProperty(children[4], "x", 2); changed = true end
            if children[4] and try(children[4], "y") ~= 18 then setProperty(children[4], "y", 18); changed = true end
            if children[4] and try(children[4], "height") ~= 4 then setProperty(children[4], "height", 4); changed = true end
            put(children[9], 0, barWidth, 0, 16)
        end
    end
end

local function scaleInterface(interfaceID, pct)
    restoreInterface(interfaceID)
    if interfaceID == 1430 and X.classicMode then pcall(X.normaliseStatusChildren) end
    if interfaceID == 1430 and not X.shapeIndex then X.shapeIndex = X.shapeNow() end
    local set = { originals = {}, order = {}, fractions = {}, held = {}, byKey = {}, dynParents = {}, noPlace = {}, trueBase = {}, fillShrink = {}, tallBar = {}, alignText = {} }
    local components, keys, dynParents = interfaceComponents(interfaceID)
    if not components or #components == 0 then return false end
    set.dynParents = dynParents

    -- 1) the components above the interface (the bars' frame sits inside components of another interface)
    local parents, seenParent, topOfInterface = {}, {}, {}
    for _, component in ipairs(components) do
        local parent = try(component, "parentStatic")
        local parentInterface = parent and try(parent, "interfaceID")
        if parent and parentInterface ~= nil and parentInterface ~= interfaceID then
            topOfInterface[component] = true
            local current, level = parent, 0
            while current and level < PARENT_LEVELS do
                local name = keyOf(current)
                if name and not seenParent[name] then
                    seenParent[name] = true
                    parents[#parents + 1] = { component = current, key = name }
                end
                current = try(current, "parentStatic")
                level = level + 1
            end
        end
    end

    -- 2) every size and position is remembered before anything is changed
    for _, component in ipairs(components) do remember(set, component) end
    -- (the text of the main bar's status bars: the font it has the first time it is seen is its own, and every later scaling starts from that one. When
    -- the game's layout is made again, as it is when the combat mode is changed, the new text can come with the font the old one was scaled to, and
    -- scaling that went on getting bigger with each change.)
    if interfaceID == 1430 then
        X.nativeFont = X.nativeFont or {}
        for _, component in ipairs(components) do
            local key = keys[component]
            local o = key and set.originals[component]
            if o and type(o.font) == "number" and o.font >= 0 and key:match("^1430:%d+:9:") then
                local statik = key:match("^(1430:%d+):")
                local native = X.nativeFont[statik]
                if native == nil then X.nativeFont[statik] = o.font
                elseif o.font ~= native then
                    if (X.fontSaid or 0) < 8 then X.fontSaid = (X.fontSaid or 0) + 1;  end
                    o.font = native
                end
            end
        end
    end
    X.applyLockExtent(set, components, keys, interfaceID)
    applyPlayerLayout(set, components, keys, interfaceID)
    local parentList = {}
    for _, parent in ipairs(parents) do
        -- a frame already scaled for another interface is not scaled again
        if not parentItem[parent.key] and remember(set, parent.component, parent.key) then parentList[#parentList + 1] = parent end
    end

    -- 3) then everything is scaled from what was remembered
    local toHold = {}
    for _, component in ipairs(components) do
        local sprite = try(component, "spriteID")
        local isFrame = type(sprite) == "number" and sprite >= FRAME_SPRITE_MIN and sprite <= FRAME_SPRITE_MAX
        local target
        local key = keys[component]
        local isChild = type(key) == "string" and select(2, key:gsub(":", "")) >= 2      -- a dynamic piece inside a bar
        if not isFrame then target = scaleOne(set, component, pct, true, isChild) end
        if target then
            local item = { component = component, target = target, percent = pct, key = keys[component], adaptive = isFill(set, component, keys[component]),
                always = topOfInterface[component], seen = {}, base = set.originals[component] }
            if item.adaptive and not set.tallBar[component] then
                -- a filling bar keeps the height it had (a scaled one comes out too thick next to the bar behind it)
                target.height = set.originals[component].height
                setProperty(component, "height", target.height)
            end
            toHold[#toHold + 1] = item
        end
    end
    for _, parent in ipairs(parentList) do
        local target = scaleOne(set, parent.component, pct, false)
        if target then
            -- the frame around the bars: checked every frame, because a frame at the wrong size is the most noticeable
            local item = { component = parent.component, target = target, percent = pct, always = true, seen = {}, base = set.originals[parent.component], owner = interfaceID, frameKey = parent.key }
            toHold[#toHold + 1] = item
            parentItem[parent.key] = item
        end
    end
    applyTwoRowTargets(set, components, keys, toHold, pct, interfaceID)
    -- the frames above the bars keep a fixed border between them (a frame 4 pixels smaller than the one around it), instead of each
    -- being scaled and rounded on its own, which left one 1 pixel off. Worked out from the outermost frame inwards.
    do
        local heldBy = {}
        for _, item in ipairs(toHold) do heldBy[item.component] = item end
        local function itemFor(component)
            if heldBy[component] then return heldBy[component] end
            local name = keyOf(component)
            return name and parentItem[name]
        end
        local function baseFor(component)
            if set.originals[component] then return set.originals[component] end
            local name = keyOf(component)
            return name and parentBase[name]
        end
        for position = #parentList, 1, -1 do
            local component = parentList[position].component
            local item = heldBy[component]
            local outer = try(component, "parentStatic")
            local outerItem = outer and itemFor(outer)
            local base, outerBase = set.originals[component], outer and baseFor(outer)
            if item and outerItem and base and outerBase then
                local gapW, gapH = outerBase.width - base.width, outerBase.height - base.height
                if gapW >= 0 and gapW <= 2 * SMALL_OFFSET and gapH >= 0 and gapH <= 2 * SMALL_OFFSET then
                    item.target.width, item.target.height = outerItem.target.width - gapW, outerItem.target.height - gapH
                    setProperty(component, "width", item.target.width)
                    setProperty(component, "height", item.target.height)
                end
            end
        end
    end
    -- the background frame of a bar (nine sprites, sprites 18257-18265, made as dynamic components of a static one): the corners keep their
    -- size and the edges grow with the static component they sit in, so the frame always fills it. A piece touching the right edge moves
    -- right by the growth, a piece in the middle gets wider by it (and the same downwards).
    do
        local parentOf, heldBy = {}, {}
        for _, dp in ipairs(dynParents) do parentOf[dp.prefix] = dp.component end
        for _, item in ipairs(toHold) do heldBy[item.component] = item end
        for _, component in ipairs(components) do
            local key, sprite = keys[component], try(component, "spriteID")
            if key and type(sprite) == "number" and sprite >= FRAME_SPRITE_MIN and sprite <= FRAME_SPRITE_MAX then
                local parent = parentOf[key:match("^(%d+:%d+):")]
                local parentBase, parentItem_ = parent and set.originals[parent], parent and heldBy[parent]
                local base = set.originals[component]
                if parentBase and parentItem_ and base and type(base.x) == "number" and type(base.y) == "number" then
                    local growW, growH = parentItem_.target.width - parentBase.width, parentItem_.target.height - parentBase.height
                    local target = { width = base.width, height = base.height, x = base.x, y = base.y }
                    local function fit(position, size, parentSize, grow)
                        local first, last = position <= 0, position + size >= parentSize
                        if first and last then return position, size + grow end       -- fills the whole width
                        if last then return position + grow, size end                  -- right / bottom piece: moves out
                        if first then return position, size end                        -- left / top piece: stays
                        return position, size + grow                                   -- the middle: stretches
                    end
                    target.x, target.width = fit(base.x, base.width, parentBase.width, growW)
                    target.y, target.height = fit(base.y, base.height, parentBase.height, growH)
                    if target.x ~= base.x or target.y ~= base.y or target.width ~= base.width or target.height ~= base.height then
                        pcall(function() component:SetWidth(target.width); component:SetHeight(target.height) end)
                        setProperty(component, "x", target.x)
                        setProperty(component, "y", target.y)
                        toHold[#toHold + 1] = { component = component, target = target, percent = pct, key = key, seen = {}, base = base, frame = true }
                    end
                end
            end
        end
    end
    local byKey, hasFill = {}, {}
    for _, item in ipairs(toHold) do
        for field in pairs(item.target) do item.seen[field] = try(item.component, field) end
        item.trueBase, item.layoutShrink = set.trueBase[item.component], set.fillShrink[item.component]
        if set.alignText[item.component] then item.align = true; centreText(item.component) end
        if item.key then
            byKey[item.key] = item
            do
                local pfx, idx = tostring(item.key):match("^(.+):(%d+):[^:]+$")
                if pfx and tonumber(idx) <= 7 then byKey[pfx .. ":" .. idx .. "#"] = item end
            end
            item.prefix = item.key:match("^(%d+:%d+):")
            if item.adaptive then hasFill[item.prefix] = true end
        end
    end
    -- the pieces that make up a bar (the backing, and the fill) keep their original height, so the bars grow longer but not thicker
    for _, item in ipairs(toHold) do
        local base = set.originals[item.component]
        if item.prefix and hasFill[item.prefix] and base and base.height <= BAR_PIECE_MAX_HEIGHT and not set.tallBar[item.component] then
            local sprite = try(item.component, "spriteID")
            -- (an upright bar with its fill fitted is the one with images of its own: its pieces are scaled in thickness. That is known from the fit,
            -- which is set before the bars are laid out, and not from the sprite, which is swapped after it (or, on turning it off, before it was put back):
            -- the thickness was always the one the sprite said before, one toggle behind.)
            local turnedPiece = X.shapeIndex and X.shapeIndex >= 3 and tostring(item.prefix):find("^1430:") and true or false
            local fitted = turnedPiece and fillFit[kindOfPrefix(item.prefix) or ""]
            if type(sprite) == "number" and (sprite >= 0 or turnedPiece) and not fitted and item.target.height ~= base.height then
                item.target.height = base.height
                setProperty(item.component, "height", base.height)
                item.seen.height = try(item.component, "height")
            end
        end
    end
    -- where the game puts the pieces of a bar itself: the backing pieces sit at the same height as the fill, and the fill keeps its
    -- original distance from the left edge
    local fillByPrefix = {}
    for _, item in ipairs(toHold) do if item.adaptive and item.prefix then fillByPrefix[item.prefix] = item end end
    for _, item in ipairs(toHold) do
        local fill = item.prefix and fillByPrefix[item.prefix]
        local base = set.originals[item.component]
        -- (in the vertical shapes the game puts the pieces of a bar, drawn turned, at their own places: ends at the top and bottom, not level with the fill)
        if fill and not (X.shapeIndex and X.shapeIndex >= 3 and tostring(item.prefix):find("^1430:")) and fill.target.y and base and base.height <= BAR_PIECE_MAX_HEIGHT and item.target.y and not set.tallBar[item.component] then
            local sprite = try(item.component, "spriteID")
            if type(sprite) == "number" and sprite >= 0 then
                item.target.y = fill.target.y
                setProperty(item.component, "y", item.target.y)
                if item == fill and item.target.x and base.x then
                    item.target.x = base.x
                    setProperty(item.component, "x", item.target.x)
                end
                item.seen.y, item.seen.x = try(item.component, "y"), try(item.component, "x")
            end
        end
    end
    -- how wide each filling bar is when full: the right edge of the bar behind it, less the same gap on both sides
    for _, item in ipairs(toHold) do
        if item.adaptive and item.prefix then
            local base = set.originals[item.component]
            local right
            for _, other in ipairs(toHold) do
                local otherBase = set.originals[other.component]
                if other ~= item and other.prefix == item.prefix and otherBase and base and otherBase.height > base.height and otherBase.x and otherBase.width then
                    local edge = otherBase.x + otherBase.width
                    if not right or edge > right then right = edge end
                end
            end
            if right and base and type(base.x) == "number" then item.fullWidth = right - 2 * base.x end
            -- (the main bar's fills: the whole bar is as wide as the box that holds its text (the ninth piece under the bar), less the same gap on both
            -- sides. After a change from the modern layout to the classic one the backing pieces were still the modern ones' when this was worked out,
            -- and the fills came out 90 wide at most, not 112: the fill was held to a width the game never gave it and fought it on every frame.)
            if base and type(base.x) == "number" and tostring(item.prefix):find("^1430:") then
                for _, other in ipairs(toHold) do
                    if other.prefix == item.prefix and other ~= item and tostring(other.key):match("^%d+:%d+:9:") then
                        local otherBase = set.originals[other.component]
                        if otherBase and type(otherBase.width) == "number" and otherBase.width > 40 then
                            local alt = otherBase.width - 2 * base.x
                            if not item.fullWidth or math.abs(alt - item.fullWidth) > 4 then
                                item.fullWidth = alt
                            end
                        end
                    end
                end
            end
        end
    end
    -- the pieces of each bar's backing (left end, middle, right end, in two rows) are made 1 pixel wider where they meet the next piece, so
    -- that the picture on each overlaps the next by a pixel: where two stretched pictures just touch, a see-through line can show
    -- between them. The left end goes under the middle, and the middle under the right end (pieces are drawn in that order).
    do
        local overlapSaid = set.overlapSaid or {}
        set.overlapSaid = overlapSaid
        local backing = {}                      -- prefix -> list of items
        local fillHeight = {}                   -- prefix -> the height of its fill (the backing pieces are taller than that)
        for _, item in ipairs(toHold) do
            local base = set.originals[item.component]
            if item.adaptive and item.prefix and base and type(base.height) == "number" then fillHeight[item.prefix] = base.height end
        end
        for _, item in ipairs(toHold) do
            local base = set.originals[item.component]
            local limit = item.prefix and fillHeight[item.prefix]
            if limit and not item.adaptive and base and type(base.x) == "number" and type(base.width) == "number" and type(base.height) == "number"
                and base.height > limit and type(try(item.component, "spriteID")) == "number" and item.target.width then
                local list = backing[item.prefix]
                if not list then list = {}; backing[item.prefix] = list end
                list[#list + 1] = item
            end
        end
        if next(backing) == nil and not set.overlapNone then
            set.overlapNone = true
            local fills, pieces = 0, 0
            for _, item in ipairs(toHold) do
                if item.adaptive then fills = fills + 1 end
                if item.prefix then pieces = pieces + 1 end
            end
        end
        for _, list in pairs(backing) do
            local xs, seenX = {}, {}
            for _, item in ipairs(list) do
                local x = set.originals[item.component].x
                if not seenX[x] then seenX[x] = true; xs[#xs + 1] = x end
            end
            table.sort(xs)
            local prefix = list[1] and list[1].prefix
            if prefix and not overlapSaid[prefix] then
                overlapSaid[prefix] = true
            end
            -- all six pieces of a frame share one top and one height: at some sizes the scaling rounded one of them differently, which showed
            -- as a piece 1 pixel lower. The first piece (the left end) is the reference; any that differ are said once and put right.
            do
                local ref = list[1]
                local refY, refH = ref and ref.target.y, ref and ref.target.height
                if type(refY) == "number" and type(refH) == "number" then
                    for index, item in ipairs(list) do
                        local t = item.target
                        if type(t.y) == "number" and type(t.height) == "number" and (t.y ~= refY or t.height ~= refH) and math.abs(t.y - refY) <= 2 and math.abs(t.height - refH) <= 2 then
                            if not set.alignSaid then
                                set.alignSaid = true
                            end
                            t.y, t.height = refY, refH
                            setProperty(item.component, "y", refY)
                            setProperty(item.component, "height", refH)
                            item.seen.y, item.seen.height = try(item.component, "y"), try(item.component, "height")
                        end
                    end
                end
            end
            if #xs == 3 then
                -- The left end, the middle and the right end of a frame are joined so that no gap shows: see the two cases below.
                -- (Scaling each piece's place and width separately left a pixel gap or overlap at some sizes.)
                local nextX = {}
                for _, item in ipairs(list) do
                    local x = set.originals[item.component].x
                    if x == xs[2] then nextX[xs[1]] = nextX[xs[1]] or item.target.x end
                    if x == xs[3] then nextX[xs[2]] = nextX[xs[2]] or item.target.x end
                end
                for _, item in ipairs(list) do
                    local x = set.originals[item.component].x
                    local width
                    if x == xs[1] then
                        -- the left end keeps its own scaled width and goes LEFT_OVERLAP pixels further under the middle (as it always has: with
                        -- less than this a line showed at the join)
                        width = item.target.width + LEFT_OVERLAP
                    elseif x == xs[2] then
                        -- the middle runs from its own place to where the right end begins, and MIDDLE_OVERSHOOT pixels past it, under the right
                        -- end (so a pixel of rounding can never leave a gap there: a gap showed as a light line)
                        local joinAt = nextX[x]
                        width = item.target.width
                        if type(joinAt) == "number" and type(item.target.x) == "number" then
                            local exact = joinAt - item.target.x
                            if exact > 0 and math.abs(exact - item.target.width) <= JOIN_TOLERANCE then width = exact end
                        end
                        width = width + MIDDLE_OVERSHOOT
                    end
                    if width then
                        item.target.width = width
                        setProperty(item.component, "width", width)
                        item.seen.width = try(item.component, "width")
                    end
                end
            end
        end
    end
    X.fixTurnedBacking(toHold, byKey, interfaceID, true)
    for _, item in ipairs(toHold) do
        if item.adaptive and item.prefix then
            item.kind = kindOfPrefix(item.prefix) or false
            -- (the fitting and the growing are worked out for a flat bar: a fill drawn turned keeps the game's place and thickness)
            local turnedBar = X.shapeIndex and X.shapeIndex >= 3 and tostring(item.prefix):find("^1430:") and true or false
            local fit = item.kind and fillFit[item.kind] and not turnedBar
            if fit then
                -- the frame's box, from its own (already scaled) pieces: the ones of this bar that are taller than the fill
                local fillBase = set.originals[item.component]
                local x0, x1, y0, frameH, leftW
                for _, other in ipairs(toHold) do
                    local ob = set.originals[other.component]
                    local t = other.target
                    if other ~= item and not other.adaptive and other.prefix == item.prefix and ob and fillBase and type(ob.height) == "number"
                        and type(ob.width) == "number" and ob.width > 0 and type(try(other.component, "spriteID")) == "number"
                        and type(fillBase.height) == "number" and ob.height > fillBase.height
                        and type(t.x) == "number" and type(t.y) == "number" and type(t.width) == "number" and type(t.height) == "number" then
                        if not x0 or t.x < x0 then x0, leftW = t.x, t.width end
                        if not x1 or t.x + t.width > x1 then x1 = t.x + t.width end
                        y0, frameH = t.y, t.height
                    end
                end
                if x0 and x1 and frameH and leftW then
                    local insetY = math.floor(frameH * FIT_RATIO + 0.5)
                    local insetX = math.floor((leftW - LEFT_OVERLAP) * FIT_RATIO + 0.5)       -- (the left end is LEFT_OVERLAP pixels wider than its picture)
                    -- (the left side reaches FIT_LEFT_EXTRA pixels further out than the border measurement says, seen in game; the right edge stays)
                    local leftX = math.max(x0, x0 + insetX - FIT_LEFT_EXTRA)
                    local width = (x1 - x0 - insetX) - leftX + x0 + FIT_RIGHT_EXTRA
                    item.target.x, item.target.y = leftX, y0 + insetY
                    item.target.height = frameH - 2 * insetY
                    -- (the width is worked out from the value, as a share of the space inside the frame)
                    item.fullWidth = width * 100 / (item.percent or 100)
                    for _, field in ipairs({ "x", "y", "height" }) do
                        setProperty(item.component, field, item.target[field])
                        item.seen[field] = try(item.component, field)
                    end
                    if not set.fitSaid then
                        set.fitSaid = true
                    end
                end
            end
            item.turnFit = nil
            if turnedBar and item.kind and fillFit[item.kind] then
                -- (the same fitting, for a bar drawn turned: its length runs down the screen and its thickness across. The frame's pieces are
                -- turned about their middles, so where each one reaches along the bar is worked out from its middle and its length.)
                local fillBase = set.originals[item.component]
                local top, bottom, firstLength, frameH
                for _, other in ipairs(toHold) do
                    local ob = set.originals[other.component]
                    local t = other.target
                    if other ~= item and not other.adaptive and other.prefix == item.prefix and (X.shapeIndex ~= 4 or (tonumber(tostring(other.key):match("^%d+:%d+:(%d+):")) or 99) <= 7) and ob and fillBase and type(ob.height) == "number"
                        and type(ob.width) == "number" and ob.width > 0 and type(fillBase.height) == "number" and ob.height > fillBase.height
                        and type(t.y) == "number" and type(t.height) == "number" and type(t.width) == "number" then
                        local middle = t.y + t.height / 2
                        local a, b = middle - t.width / 2, middle + t.width / 2
                        if not top or a < top then top, firstLength = a, t.width end
                        if not bottom or b > bottom then bottom = b end
                        frameH = t.height
                    end
                end
                if top and bottom and frameH and firstLength then
                    local insetY = math.floor(frameH * FIT_RATIO + 0.5)
                    local insetX = math.floor((firstLength - LEFT_OVERLAP) * FIT_RATIO + 0.5)
                    local startAt = math.max(top, top + insetX - FIT_LEFT_EXTRA)
                    local length = (bottom - top - insetX) - startAt + top + FIT_RIGHT_EXTRA
                    local thickness = frameH - 2 * insetY
                    -- (7x2: no extra thickness here. That was tuned for the game's own fill; a fitted sprite fill came out wider than its backing with it)
                    if X.shapeIndex ~= 3 then thickness = thickness + X.turnedWiden(item) end
                    -- (7x2: the fitted fill was still seven pixels too thick, three on the left and four on the right, with the backing eight thick; as much as the backing grows with the status bar size)
                    if X.shapeIndex == 3 then
                        -- (all of it worked out at 100% and then scaled, as the 1x14 shape is, so that it grows with the scale)
                        local scale = (item.percent or percent) / 100
                        local at100 = frameH / scale
                        local pixels = math.max(2, at100 - 8) + math.max(0, math.floor(0.75 * (at100 - 16) + 0.5)) + (X.turnedBigAdjust())
                        thickness = math.max(2, math.floor(pixels * scale + 0.5))
                    end
                    -- (the fill of that adrenaline bar stays where it was: the frame was lengthened, not the fill)
                    if X.shapeIndex == 4 and summoningHidden and item.kind == "adrenaline" then startAt = startAt + 1; length = length - 2 end
                    local grown = fillGrow[item.kind]
                    if grown then thickness = thickness + grown.height; startAt = startAt - grown.left; length = length + grown.width + grown.left end
                    -- (7x2 at the default status bar size: the fill came out about two and a half pixels (at 100%) too thick)
                    if X.shapeIndex == 3 and barHeight <= 0 then thickness = math.max(2, thickness - math.floor(2.5 * (item.percent or percent) / 100 + 0.5)) end
                    -- (7x2, the modern fill: a pixel longer at the bottom and two thicker on its right)
                    if X.shapeIndex == 3 then length = length + math.floor((1 - (barHeight >= 20 and 2 or 0)) * (item.percent or percent) / 100 + 0.5) end
                    -- (7x2: the fill 2 wider, on its right: see turnedSide; its 6 pixels more length is in turnedFill. Pixels on the screen)
                    if X.shapeIndex == 3 then thickness = thickness + 2 end
                    item.turnFit = { top = startAt, full = length, thickness = thickness }
                    item.target.height = thickness
                    setProperty(item.component, "height", thickness)
                    item.seen.height = try(item.component, "height")
                end
            end
            local grow = item.kind and not turnedBar and fillGrow[item.kind]
            if grow and grow.height ~= 0 and item.target.height then
                item.growH = grow.height
                item.target.height = item.target.height + grow.height
                setProperty(item.component, "height", item.target.height)
                item.seen.height = try(item.component, "height")
            end
            if grow and grow.left ~= 0 and type(item.target.x) == "number" then
                item.growL = grow.left
                item.target.x = item.target.x - grow.left
                setProperty(item.component, "x", item.target.x)
                item.seen.x = try(item.component, "x")
            end
        end
    end
    X.fixTurnedBacking(toHold, byKey, interfaceID, false)
    for _, dp in ipairs(dynParents) do dp.fill = hasFill[dp.prefix] == true end
    set.held, set.byKey, set.anchor = toHold, byKey, components[1]
    sets[interfaceID] = set
    layoutVersion = layoutVersion + 1
    structVersion = structVersion + 1
    busyVersion = busyVersion + 1
    Perf.tally("structure changes (scaleInterface)")
    -- a filling bar gets the width its value gives it straight away (from the text beside it), by the same sum used to keep it right
    -- later. It was scaled from the width it happened to have, which came out a pixel different at some sizes (120%, say), and that
    -- showed until the interface was locked or unlocked.
    pcall(rescanSet, set, true)
    for _, item in ipairs(toHold) do
        local fraction = item.adaptive and item.fullWidth and item.prefix and set.fractions[item.prefix]
        if fraction then
            local wanted = math.floor(fraction * item.fullWidth * item.percent / 100 + 0.5)
            local grow = fillGrow[kindOfPrefix(item.prefix) or ""]
            if grow and wanted > 0 then wanted = wanted + grow.width + grow.left end
            item.target.width = wanted
            setProperty(item.component, "width", wanted)
            item.seen.width = try(item.component, "width")
        end
    end
    updateHolding()
    return true
end

----------------------------------------------------------------
-- RESIZING THE MAIN BAR BY ITS CORNER
-- The player can drag the corner of the main bar to give it one of four shapes (14 buttons in one row, two rows of 7, two columns of 7,
-- one column of 14). The game lays the whole bar out again, in one step, at the game's own sizes: the root (1430:0) becomes 526x72,
-- 261x124, 124x261 or 72x526. Holding the old layout fought this (the pieces were put back where they were in the old shape). So, before
-- any piece is put back, the root is looked at at the start of every game event; when it has taken another of the four shapes, the pieces
-- the game has not touched are put back to their own sizes, and the whole bar is scaled again from what the game has now.
----------------------------------------------------------------
X.BAR_SHAPES = { { 526, 72 }, { 261, 124 }, { 124, 261 }, { 72, 526 } }

-- the pieces the game has not written to are still at the scaled size and place of the old shape: they go back to their own (fonts and
-- text alignment too, or scaling again would take the scaled font as the game's and make it bigger every time)
function X.unscaleForResize(set)
    local count = 0
    -- (every held text goes back to the font the game gave it, whatever state the piece is in: a font left at its bigger size was taken as the
    -- game's when the bar was scaled again, and grew a step every time the mode changed)
    for _, item in ipairs(set.held) do
        local component = item.component
        if component and not item.frame and not item.frameKey then
            local base = set.trueBase[component] or set.originals[component]
            if base and type(base.font) == "number" and base.font >= 0 then
                local cur = try(component, "font")
                if type(cur) == "number" and cur ~= base.font then
                    setProperty(component, "font", base.font)
                    count = count + 1
                end
            end
        end
    end
    for _, item in ipairs(set.held) do
        local component = item.component
        if component and item.seen and not item.frame and not item.frameKey and not item.owner then
            local base = set.trueBase[component] or set.originals[component]
            if base then
                for field, target in pairs(item.target) do
                    if field == "font" then
                        if type(target) == "number" and type(base.font) == "number" and target ~= base.font and try(component, "font") == target then
                            setProperty(component, "font", base.font)
                            count = count + 1
                        end
                    elseif type(target) == "number" and type(base[field]) == "number" then
                        local cur, ref = try(component, field), item.seen[field]
                        if type(ref) ~= "number" then ref = target end
                        if type(cur) == "number" and math.abs(cur - ref) <= changeTolerance(field) and math.abs(cur - base[field]) > changeTolerance(field) then
                            setProperty(component, field, base[field])
                            count = count + 1
                        end
                    end
                end
            end
        end
        if item.align and component then uncentreText(component); item.align = nil end
    end
    for component in pairs(set.alignText) do uncentreText(component) end
    return count
end

function X.startResize(set, width, height)
    X.resizing, X.resizeSize, X.resizeAt, X.resizeFp = true, width .. "x" .. height, X.logicCount or 0, nil
    set.paused = true
    local count = X.unscaleForResize(set)
end

function X.shapeFrame(set)
    local item = set.shapeItem
    if item and set.shapeFor == #set.held then return item end
    item = nil
    for _, candidate in ipairs(set.held) do
        if candidate.frameKey == "1477:72" and candidate.component then item = candidate; break end
    end
    set.shapeItem, set.shapeFor = item, #set.held
    return item
end

function X.shapeRoot(set)
    local item = set.shapeRootItem
    if item and set.shapeRootFor == #set.held then return item end
    item = nil
    for _, candidate in ipairs(set.held) do
        if candidate.component and not candidate.frameKey and not candidate.key and keyOf(candidate.component) == "1430:0" then item = candidate; break end
    end
    set.shapeRootItem, set.shapeRootFor = item, #set.held
    return item
end

-- a number that changes when any of a sample of the bar's pieces moves or changes size (the game lays the bar out when the button is let go)
function X.resizeFingerprint(set)
    local held = set.held
    local step = math.max(1, #held // 40)
    local total = 0
    for position = 1, #held, step do
        local component = held[position].component
        if component then
            for _, field in ipairs({ "x", "y", "width", "height" }) do
                local value = try(component, field)
                total = (total * 31 + (type(value) == "number" and value or 0) + 7) % 1000000007
            end
        end
    end
    return total
end

-- What the game itself gives the pieces of the main bar that change with its shape (the status bars, the frame, the scroller and buttons), in each of
-- the four shapes at size 100 (x, y, width, height), from the layout log. At a size above 100 some of them stayed in the 1x14 places. They are put to these (at 100) before
-- the bar is scaled, so they are scaled from the right values.
X.SHAPE_PIECES = {
    [6] = { { 0, 3, 504, 30 }, { 0, 0, 245, 50 }, { 71, 16, 50, 229 }, { 39, 16, 30, 488 } },
    [7] = { { 0, 0, 126, 30 }, { 0, 0, 122, 30 }, { 0, 0, 30, 114 }, { 0, 0, 30, 122 } },
    [9] = { { 30, 3, 94, 24 }, { 30, 4, 90, 22 }, { 4, 30, 22, 82 }, { 3, 30, 24, 90 } },
    [10] = { { 0, 0, 126, 30 }, { 0, 0, 122, 30 }, { 0, 0, 30, 114 }, { 0, 0, 30, 122 } },
    [14] = { { 252, 0, 126, 30 }, { 0, 24, 122, 30 }, { 24, 0, 30, 114 }, { 0, 244, 30, 122 } },
    [16] = { { 30, 3, 94, 24 }, { 30, 4, 90, 22 }, { 4, 30, 22, 82 }, { 3, 30, 24, 90 } },
    [20] = { { 378, 0, 126, 30 }, { 122, 24, 122, 30 }, { 24, 114, 30, 114 }, { 0, 366, 30, 122 } },
    [22] = { { 30, 3, 94, 24 }, { 30, 4, 90, 22 }, { 4, 30, 22, 82 }, { 3, 30, 24, 90 } },
    [55] = { { 126, 0, 126, 30 }, { 122, 0, 122, 30 }, { 0, 114, 30, 114 }, { 0, 122, 30, 122 } },
    [57] = { { 30, 3, 94, 24 }, { 30, 4, 90, 22 }, { 4, 30, 22, 82 }, { 3, 30, 24, 90 } },
    [60] = { { 0, 0, 504, 30 }, { 0, 0, 245, 50 }, { 0, 0, 50, 229 }, { 0, 0, 30, 488 } },
    [61] = { { 0, 36, 504, 36 }, { 0, 52, 245, 72 }, { 0, 0, 72, 245 }, { 0, 0, 36, 504 } },
    [75] = { { 36, 0, 36, 36 }, { 35, 0, 36, 36 }, { 0, 35, 36, 36 }, { 0, 36, 36, 36 } },
    [88] = { { 72, 0, 36, 36 }, { 70, 0, 36, 36 }, { 0, 70, 36, 36 }, { 0, 72, 36, 36 } },
    [101] = { { 108, 0, 36, 36 }, { 105, 0, 36, 36 }, { 0, 105, 36, 36 }, { 0, 108, 36, 36 } },
    [114] = { { 144, 0, 36, 36 }, { 140, 0, 36, 36 }, { 0, 140, 36, 36 }, { 0, 144, 36, 36 } },
    [127] = { { 180, 0, 36, 36 }, { 175, 0, 36, 36 }, { 0, 175, 36, 36 }, { 0, 180, 36, 36 } },
    [140] = { { 216, 0, 36, 36 }, { 210, 0, 36, 36 }, { 0, 210, 36, 36 }, { 0, 216, 36, 36 } },
    [153] = { { 252, 0, 36, 36 }, { 0, 35, 36, 36 }, { 35, 0, 36, 36 }, { 0, 252, 36, 36 } },
    [166] = { { 288, 0, 36, 36 }, { 35, 35, 36, 36 }, { 35, 35, 36, 36 }, { 0, 288, 36, 36 } },
    [179] = { { 324, 0, 36, 36 }, { 70, 35, 36, 36 }, { 35, 70, 36, 36 }, { 0, 324, 36, 36 } },
    [192] = { { 360, 0, 36, 36 }, { 105, 35, 36, 36 }, { 35, 105, 36, 36 }, { 0, 360, 36, 36 } },
    [205] = { { 396, 0, 36, 36 }, { 140, 35, 36, 36 }, { 35, 140, 36, 36 }, { 0, 396, 36, 36 } },
    [218] = { { 432, 0, 36, 36 }, { 175, 35, 36, 36 }, { 35, 175, 36, 36 }, { 0, 432, 36, 36 } },
    [231] = { { 468, 0, 36, 36 }, { 210, 35, 36, 36 }, { 35, 210, 36, 36 }, { 0, 468, 36, 36 } },
    [246] = { { 0, 0, 504, 36 }, { 0, 0, 245, 72 }, { 0, 0, 72, 245 }, { 0, 0, 36, 504 } },
    [247] = { { 0, 0, 2, 36 }, { 0, 0, 2, 72 }, { 0, 0, 2, 245 }, { 0, 0, 2, 504 } },
    [248] = { { 0, 34, 318, 2 }, { 0, 70, 59, 2 }, { 0, 243, -114, 2 }, { 0, 502, -150, 2 } },
    [249] = { { 502, 0, 2, -1 }, { 243, 0, 2, 35 }, { 70, 0, 2, 208 }, { 34, 0, 2, 467 } },
    [250] = { { 196, 36, 2, 0 }, { 67, 36, 2, 36 }, { -20, 36, 2, 209 }, { -38, 36, 2, 468 } },
    [251] = { { 76, 17, 428, 2 }, { 76, 35, 169, 2 }, { 76, 122, -4, 2 }, { 76, 251, -40, 2 } },
    [252] = { { 0, 0, 504, 2 }, { 0, 0, 245, 2 }, { 0, 0, 72, 2 }, { 0, 0, 36, 2 } },
    [254] = { { 507, 38, 16, 32 }, { 245, 54, 16, 68 }, { 2, 245, 68, 16 }, { 2, 507, 32, 16 } },
    [255] = { { 0, 16, 16, 16 }, { 0, 52, 16, 16 }, { 52, 0, 16, 16 }, { 16, 0, 16, 16 } },
    [268] = { { 507, 17, 16, 16 }, { 245, 37, 16, 16 }, { 72, 2, 16, 16 }, { 39, 2, 16, 16 } },
}

-- The classic 1x14 layout of the main bar at size 100 (index 5 of each row), from the layout log made in classic mode.
do
    local classicPieces = {
        [6] = { 0, 3, 518, 30 }, [7] = { 0, 0, 129, 30 }, [9] = { 30, 3, 97, 24 }, [10] = { 0, 0, 129, 30 }, [14] = { 258, 0, 129, 30 },
        [16] = { 30, 3, 97, 24 }, [20] = { 387, 0, 129, 30 }, [22] = { 30, 3, 97, 24 }, [55] = { 129, 0, 129, 30 }, [57] = { 30, 3, 97, 24 },
        [60] = { 0, 0, 518, 30 }, [61] = { 0, 36, 518, 36 },
        [75] = { 37, 0, 36, 36 }, [88] = { 74, 0, 36, 36 }, [101] = { 111, 0, 36, 36 }, [114] = { 148, 0, 36, 36 }, [127] = { 185, 0, 36, 36 },
        [140] = { 222, 0, 36, 36 }, [153] = { 259, 0, 36, 36 }, [166] = { 296, 0, 36, 36 }, [179] = { 333, 0, 36, 36 }, [192] = { 370, 0, 36, 36 },
        [205] = { 407, 0, 36, 36 }, [218] = { 444, 0, 36, 36 }, [231] = { 481, 0, 36, 36 },
        [246] = { 0, 0, 518, 36 }, [247] = { 0, 0, 2, 36 }, [248] = { 0, 34, 332, 2 }, [249] = { 516, 0, 2, -1 }, [250] = { 203, 36, 2, 0 },
        [251] = { 76, 17, 442, 2 }, [252] = { 0, 0, 518, 2 }, [254] = { 525, 38, 16, 32 }, [255] = { 0, 16, 16, 16 }, [268] = { 525, 17, 16, 16 },
    }
    for number, values in pairs(classicPieces) do
        X.SHAPE_PIECES[number] = X.SHAPE_PIECES[number] or {}
        X.SHAPE_PIECES[number][5] = values
    end
end

-- (the frame of each shape when the bar is minimised: seen as 58x265 and 265x58 windows, 4 more than the frames: 54x261 and 261x54; the others are
-- the same sizes turned about, and 526x34 is what the 1x14 bar has, as 530x38)
X.COLLAPSED_SHAPES = { { 526, 34 }, { 261, 54 }, { 54, 261 }, { 34, 526 } }
-- which shape a frame size belongs to; the second answer is true when it is the size the shape has when minimised
function X.shapeIndexOf(width, height)
    for index, shape in ipairs(X.BAR_SHAPES) do
        if math.abs(width - shape[1]) <= 2 and math.abs(height - shape[2]) <= 2 then return index, false end
    end
    for index, shape in ipairs(X.COLLAPSED_SHAPES) do
        if math.abs(width - shape[1]) <= 2 and math.abs(height - shape[2]) <= 2 then return index, true end
    end
    return nil
end

function X.putShapePieces(set, index)
    local count = 0
    for _, item in ipairs(set.held) do
        local component = item.component
        if component and not item.key and not item.frame and not item.frameKey and not item.owner and not item.adaptive then
            local number = tonumber(string.match(tostring(keyOf(component) or ""), "^1430:(%d+)$"))
            local row = number and X.SHAPE_PIECES[number]
            local values = row and row[index]
            if values and X.otherBoth(1430) then values = X.mainExtended(number, index, values) end
            if values then
                for position, field in ipairs({ "x", "y", "width", "height" }) do
                    if try(component, field) ~= values[position] then setProperty(component, field, values[position]); count = count + 1 end
                end
            end
        end
    end
    return count
end

-- The fill of a status bar drawn turned (the two vertical shapes): from the value (the fraction read from the text beside the bar) and the
-- length of the bar behind it, as the game lays it out: the fill is the bar's length less 4 (at size 100), it hangs from the top, and sits
-- 4 in from the middle of the bar. Worked out from the numbers seen in game (103 long in a bar 108 long at 120%, at y 52 = half the length).
-- Returns nothing when the value is not known (the game's own numbers are scaled then).
-- (how far down a thicker fill hangs from half its length: the fill is drawn turned, so it grows around its own middle; scaled)
-- how far the turned bar's end pieces reach under the middle one (0 = they meet exactly)
X.SEAM = 0

function X.turnedOffset(item)
    local scale = (item.percent or percent) / 100
    -- (the fill hangs from the top of the bar by its own top edge: its box is turned about its middle, so a thicker box sits higher by half of it)
    local fit = item.turnFit
    -- (7x2: the fitted fill sits where the game's own fill does, which is right at every scale, and only its thickness is its own; the thickness is
    -- what its place is worked out from, so that the same top and the same middle line come out)
    local pfit = X.shapeIndex == 3 and nil or fit
    local top = pfit and pfit.top or 2 * scale
    local thickness = fit and fit.thickness or ((barHeight > 0 and (barHeight - 4) or 4) * scale + X.turnedWiden(item))
    local off = top - thickness / 2
    -- (the fill in the upright 2x7 shape sat a little high: it is put down by three, unless the fill is fitted to its frame, which places it)
    if X.shapeIndex == 3 and not pfit then off = off + 3 * scale end
    if X.shapeIndex == 3 then off = off - 1 * scale end
    -- (7x2: two pixels further up)
    if X.shapeIndex == 3 then off = off - (pfit and 2 or 4) * scale end
    -- (the bar's box is a pixel taller at the top from status bar size 20, with what is in it a pixel lower: the fill goes with it)
    if X.shapeIndex == 3 and barHeight >= 20 then off = off + 3 * scale end
    -- (7x2, above 100%: a pixel less at the top, see the length of the fill)
    if X.shapeIndex == 3 and scale > 1 then off = off + ((item.percent or percent) < 130 and 3 or 2) end
    -- (7x2: the constants above were tuned at 120%; at 130% the fill sat about 2-3 pixels too low, so it moves up a quarter pixel for each percent above 120)
    -- (1x14 upright: the backing went a pixel down and the fill reaches a pixel further up than where it is fitted)
    if X.shapeIndex == 4 and fit then off = off - 1 * scale end
    -- (and the fill two further up, as the backing is)
    if X.shapeIndex == 4 then off = off - 2 * scale end
    -- (and the bar's own box is two taller at the top, so everything in it hangs two further down from the top of it; a fitted fill has that in the frame)
    if X.shapeIndex == 4 and not fit then off = off + 2 end
    if X.shapeIndex == 3 then off = off + (X.tweak7x2().down or 0) end
    if X.shapeIndex == 4 then off = off + (X.tweak14x1().top or 0) end
    return off
end

-- (sideways it needs no nudge)
-- (7x2 only: the backing is a pixel further left and the fill three wider on its left side, so its middle is a pixel and a half left of where it
-- was, which is half a pixel left of the backing's new middle)
function X.turnedSide(item, fromMiddle)
    -- (the adrenaline fill of the 1x14 upright shape with summoning hidden: a pixel left, as its backing is; the middle piece it follows has moved by itself)
    if X.shapeIndex == 4 and not fromMiddle and summoningHidden and item.kind == "adrenaline" then return -1 end
    if X.shapeIndex ~= 3 then return 0 end
    -- (and a pixel to the right at 130%, none at 100%: it went by percent above 120 before and at 100% that put the fill seven pixels left of its frame)
    -- (a fitted fill: half a pixel left, as it is three thinner on the left and four on the right)
    -- (and a fitted fill is two wider on its right: its middle moves a pixel right, so that its left edge stays)
    -- (the tuned moves: the fill left; and, as the fill follows the middle of the backing, a move of that middle to the left is given back)
    local tune = X.tweak7x2()
    return (fromMiddle and -1.0 or -3.0) * (item.percent or percent) / 100 + ((0) + 0.5 + (barHeight >= 20 and -0.5 or 0)) * (item.percent or percent) / 100 + (item.turnFit and 1 or 0)
        - (tune.left or 0) + (fromMiddle and (tune.mid or 0) or 0)
end

-- (7x2: the fill reaches a pixel further down when the bar is full; as much of it as the value gives)
function X.turnedLonger(item, fraction)
    local pixels = X.shapeIndex == 3 and 1 or (X.shapeIndex == 4 and (2 + ((summoningHidden and item.kind == "adrenaline") and (item.turnFit and 1 or 1) or 0)) or 0)
    if pixels == 0 then return 0 end
    return math.floor((item.percent or percent) / 100 * pixels * (fraction or 1) + 0.5)
end

-- (7x2, the modern fill at the large status bar sizes, as seen: the thickness to add and the pixels its middle moves, by the status bar size)
function X.turnedBigAdjust()
    local steps = { { 20, 1, -0.5 }, { 18, 3, -0.5 }, { 16, 4, 0 }, { 14, 2, 0 } }
    for _, step in ipairs(steps) do
        if barHeight >= step[1] then return step[2], step[3] end
    end
    return 0, 0
end

-- 7x2 only: small moves tuned in game for each scale and status bar size (barHeight; 0 is the default size). Pixels on the screen.
--   down / left: the fill moves down / left (negative: up / right)    taller: the fill is longer at the bottom
--   mid: the middle pieces of the backing (both layers) move left, which the fill does not follow
X.TWEAKS_7X2 = {
    [100] = { [20] = { down = -1, taller = -5 } },
    [110] = { [12] = { down = 1, mid = 1 }, [14] = { down = 1, mid = 1 }, [18] = { down = 1 }, [20] = { down = -2, taller = 2 }, [0] = { down = 1, left = 1, mid = 1 } },
    [120] = { [14] = { mid = 1 }, [16] = { mid = 1 } },
    [130] = { [16] = { mid = 1 }, [18] = { mid = 1 } },
    [140] = { [0] = { left = 1, mid = 1 }, [12] = { mid = 1 }, [18] = { mid = 1 }, [20] = { down = -1 } },
    [150] = { [14] = { mid = 1 }, [18] = { mid = 1 }, [20] = { down = -1, taller = -5 } },
}
X.NO_TWEAK = {}
function X.tweak7x2()
    if X.shapeIndex ~= 3 then return X.NO_TWEAK end
    local byPercent = X.TWEAKS_7X2[percent]
    local found = byPercent and byPercent[barHeight > 0 and barHeight or 0] or X.NO_TWEAK
    local key = percent .. "/" .. barHeight .. "/" .. tostring(found ~= X.NO_TWEAK)
    if key ~= X.tweakSaid then
        X.tweakSaid = key
    end
    return found
end

-- 14x1 upright (the same kind of tuning): top = pixels taken off the top of the fill (its bottom stays where it is)
X.TWEAKS_14X1 = {
    [100] = { [12] = { top = 3 }, [14] = { top = 3 }, [16] = { top = 3 }, [18] = { top = 3 }, [20] = { top = 3 } },
    [110] = { [12] = { top = 3 }, [14] = { top = 3 }, [16] = { top = 3 }, [18] = { top = 3 }, [20] = { top = 3 } },
    [120] = { [14] = { top = 3 } },
    [140] = { [12] = { top = 3 } },
    [150] = { [12] = { top = 3 }, [16] = { top = 3 }, [20] = { top = 3 } },
}
function X.tweak14x1()
    if X.shapeIndex ~= 4 then return X.NO_TWEAK end
    local byPercent = X.TWEAKS_14X1[percent]
    return byPercent and byPercent[barHeight > 0 and barHeight or 0] or X.NO_TWEAK
end

-- (7x2: the fill is 6 pixels longer at the bottom, on the screen (and what the tuning above adds); 14x1: less what is taken off its top. This is
-- added to the length it is worked out from, and taken off again when a share is worked out from a length)
function X.turnedMore()
    if X.shapeIndex == 4 then return -(X.tweak14x1().top or 0) end
    return X.shapeIndex == 3 and (6 + (X.tweak7x2().taller or 0)) or 0
end

function X.turnedWiden(item)
    if X.shapeIndex ~= 3 then return 0 end
    return math.floor(2 * (item.percent or percent) / 100 + 0.5)
end

-- how long the backing of a bar drawn turned is: from the top of its first end to the bottom of its last one (each end is a flat piece turned about its
-- middle, so it reaches half its width above and below its middle). Worked out again only when the layout has changed.
function X.turnedBackingLength(item, parent)
    if item.backingAt == layoutVersion then return item.backingLength end
    item.backingAt, item.backingLength = layoutVersion, nil
    local first, last, index = nil, nil, 0
    pcall(function()
        parent:IterateDynamicComponents(function(child)
            index = index + 1
            if index == 5 then first = child elseif index == 7 then last = child end
        end)
    end)
    if first and last then
        local y1, h1, w1 = try(first, "y"), try(first, "height"), try(first, "width")
        local y3, h3, w3 = try(last, "y"), try(last, "height"), try(last, "width")
        if type(y1) == "number" and type(h1) == "number" and type(w1) == "number" and type(y3) == "number" and type(h3) == "number" and type(w3) == "number" then
            local top, bottom = y1 + h1 / 2 - w1 / 2, y3 + h3 / 2 + w3 / 2
            if bottom - top > 20 then item.backingLength = math.floor(bottom - top + 0.5) end
        end
    end
    return item.backingLength
end

function X.turnedFill(set, item, field, given)
    local fraction = given or (set.fractions and set.fractions[item.prefix])
    if type(fraction) ~= "number" then return nil end
    if fraction > 1 then fraction = 1 elseif fraction < 0 then fraction = 0 end
    local parent = item.turnParent
    if parent == nil then
        local number = tonumber(tostring(item.prefix):match(":(%d+)$"))
        if number then pcall(function() parent = ui.Interfaces:GetComponent(1430, number) end) end
        parent = parent or false
        item.turnParent = parent
    end
    if not parent then return nil end
    local length, breadth = try(parent, "height"), try(parent, "width")
    if type(length) ~= "number" or type(breadth) ~= "number" then return nil end
    -- (7x2: the fill is worked out from how long the backing really is, the two ends of it as they are drawn turned. The bar's own box was used, and at
    -- some sizes it is two pixels longer than the backing (107 against 105 at 130%), so the fill ran past the bottom of its frame.)
    if X.shapeIndex == 3 then
        local ext = X.turnedBackingLength(item, parent)
        if ext then length = ext end
    end
    local pct = item.percent or percent
    -- (7x2, above 100%: a pixel less at the top; the bottom stays where it is)
    local cut = (X.shapeIndex == 3 and pct > 100) and (pct < 130 and 3 or 2) or 0
    local fill = math.floor(fraction * (((X.shapeIndex ~= 3 and item.turnFit) and item.turnFit.full or (length - 4 * pct / 100)) + X.turnedMore() - cut) + 0.5) + X.turnedLonger(item, fraction)
    if X.shapeIndex == 3 then
        -- (the fill's length goes with its thickness in the same way, so that its edges fall on whole pixels like the backing's)
        local thick = item.turnFit and item.turnFit.thickness or try(item.component, "height")
        -- (the tuned extra length is left out of this: it is the player's to set to the pixel, and counted in it a one pixel change was undone half the time)
        local tuned = math.floor((X.tweak7x2().taller or 0) * fraction + 0.5)
        if type(thick) == "number" and fill > 0 and (fill - tuned + thick) % 2 ~= 0 then fill = fill - 1 end
    end
    if field == "width" then return fill end
    if field == "y" then return math.floor(fill / 2 + X.turnedOffset(item) + 0.5) end
    if field == "x" then return math.floor(breadth / 2 + 4.17 * pct / 100 - fill / 2 + X.turnedSide(item) + 0.5) end
    return nil
end

-- The fill of a turned status bar is put right on its own, each frame, whatever the held list does with it (with the modern bars on, the sprite
-- reads -1 and the fill is not always known as a fill there). When the game lays the bar out again it writes the fill's length at its own size
-- and its sideways place but not how far down it hangs: a length and a place that do not go together (y is half the length when the game or
-- this puts it). That is how it is told. The length is then taken as a share of the full length at the game's size and worked out again.
function X.repairTurned()
    if not X.shapeIndex or X.shapeIndex < 3 then return end
    local now = X.logicCount or 0
    if X.holdPaused or X.rebuilding or X.resizing then return end
    for _, field in ipairs({ "lockRescaleAt", "lockRescaleAgainAt" }) do
        if X[field] and now >= X[field] then
            X[field] = nil
            pcall(Engine.setPercent, percent)
            return
        end
    end
    -- A check every few ticks that the pieces of the status bars are as they were set: the game can lay them out again at any time (locking
    -- the interface did, and the fills came back four thick and at its own places). If one is not, everything is laid out again, at most a few
    -- times in a row and not more often than every 60 ticks.
    if now >= (X.watchAt or 0) and sets[1430] and not sets[1430].paused then
        X.watchAt = now + 8
        local wrong = nil
        for _, item in ipairs(sets[1430].held or {}) do
            local index = tonumber(tostring(item.key):match("^1430:%d+:(%d+):"))
            if index and index <= 7 and item.component and item.target then
                local height, x = try(item.component, "height"), try(item.component, "x")
                local wantedHeight = (index == 4 and item.turnFit) and item.turnFit.thickness or item.target.height
                if type(height) == "number" and type(wantedHeight) == "number" and math.abs(height - wantedHeight) > 1 then wrong = item.key; break end
                if index ~= 4 and type(x) == "number" and type(item.target.x) == "number" and math.abs(x - item.target.x) > 1 then wrong = item.key; break end
            end
        end
        if not wrong then
            X.watchRescues = 0
        elseif (X.watchRescues or 0) < 3 and now >= (X.watchCool or 0) then
            X.watchRescues, X.watchCool = (X.watchRescues or 0) + 1, now + 60
            for _, item in ipairs(sets[1430].held or {}) do
                local index = tonumber(tostring(item.key):match("^1430:%d+:(%d+):"))
                if index and index <= 7 and item.component then pcall(checkItem, sets[1430], item) end
            end
            return
        end
    end
    local set = sets[1430]
    if not set or set.paused or not set.held then return end
    local cells = X.SHAPE_CELLS[X.shapeIndex]
    local full = cells and (cells.cell - 36)
    -- (the fills are picked out of the held list once, not searched for every frame)
    if X.turnedList == nil or X.turnedListFor ~= set.held or X.turnedListSize ~= #set.held then
        local list = {}
        for _, item in ipairs(set.held) do
            if item.component and tostring(item.key):find("^1430:%d+:4#") then list[#list + 1] = item end
        end
        X.turnedList, X.turnedListFor, X.turnedListSize = list, set.held, #set.held
    end
    -- (the fills are drawn from their kept value by checkItem, which is also what runs before each frame: nothing here writes a fill's length, as a
    -- second reader of what the game wrote took the value before checkItem did and left it stale)
    for _, item in ipairs(X.turnedList) do
        item.prefix = item.prefix or tostring(item.key):match("^(%d+:%d+):")
        pcall(checkItem, set, item)
    end
end

function X.rebuildShape(set, width, height)
    X.rebuilding = true
    local count = X.unscaleForResize(set)
    -- (the game does not give the root the new shape's size: it is as big as the frame in each of the four shapes)
    local root = X.shapeRoot(set)
    if root then
        -- (a minimised bar has a smaller frame, but its root is the whole size of the shape)
        local rw, rh = width, height
        local shapeOf, minimised = X.shapeIndexOf(width, height)
        if shapeOf and minimised then rw, rh = X.BAR_SHAPES[shapeOf][1], X.BAR_SHAPES[shapeOf][2] end
        local rootWidth, rootHeight = try(root.component, "width"), try(root.component, "height")
        if type(rootWidth) ~= "number" or math.abs(rootWidth - rw) > 2 or type(rootHeight) ~= "number" or math.abs(rootHeight - rh) > 2 then
            pcall(function() root.component:SetWidth(rw); root.component:SetHeight(rh) end)
            if try(root.component, "width") ~= rw or try(root.component, "height") ~= rh then
                pcall(function() root.component:SetSize(rw, rh) end)
            end
        end
    end
    -- (the frames above the bar were given the new shape's size by the game: that is what they are scaled from)
    for key, item in pairs(parentItem) do
        if item.owner == 1430 then parentBase[key] = nil end
    end
    local classic = width >= 540
    X.shapeIndex = classic and 1 or X.shapeIndexOf(width, height) or X.shapeIndex
    if X.shapeIndex then count = count + X.putShapePieces(set, classic and 5 or X.shapeIndex) end
    forgetSet(1430)
    local ok, scaled = pcall(scaleInterface, 1430, percent)
    layoutVersion = layoutVersion + 1
    structVersion = structVersion + 1
    busyVersion = busyVersion + 1
    forceFrames = math.max(forceFrames, FORCE_FRAMES)
    if ok and scaled and sets[1430] then sets[1430].posReady = true end
    if afterFrameHook then pcall(afterFrameHook) end
    X.rebuilding, X.resizing = false, false
    if Engine.shapeCallback and not X.quietShape then pcall(Engine.shapeCallback, X.shapeIndex) end      -- (not for the Other Settings: the shape is the same and the page would jump to the top)
end

----------------------------------------------------------------
-- THE EXTRA BARS' SHAPES (bars 2 to 5: interfaces 1670 to 1673)
-- At 100% the game lays the slots out itself when the bar is resized; with the bars scaled it does not (the bar stays as it was held). So the
-- shape is read from the proportions of the bar's window (the same at any size), and when a new one has stayed for a moment the bar is put back
-- to its normal size, laid out as the game lays it out at 100% (from the layout log), and scaled again.
-- The numbers are at size 100: root w,h | scroller piece (1) x,y,w,h | piece 2 x,y | container x,y,w,h | where slot k (0 to 13) goes.
----------------------------------------------------------------
X.EXTRA_SHAPE_BARS = { { 1670, 74 }, { 1671, 79 }, { 1672, 84 }, { 1673, 89 } }
X.EXTRA_CLASSIC = { root = { 548, 34 }, p1 = { 525, 1, 16, 32 }, p2 = { 0, 16 }, box = { 0, -1, 518, 36 }, slot = function(k) return 37 * k, 0 end }
X.EXTRA_SHAPES = {
    { root = { 526, 34 }, p1 = { 507, 1, 16, 32 }, p2 = { 0, 16 }, box = { 0, -1, 504, 36 }, slot = function(k) return 36 * k, 0 end },
    { root = { 261, 72 }, p1 = { 245, 1, 16, 70 }, p2 = { 0, 54 }, box = { 0, 0, 245, 72 }, slot = function(k) if k < 7 then return 35 * k, 0 end return 35 * (k - 7), 35 end },
    { root = { 72, 261 }, p1 = { 1, 245, 70, 16 }, p2 = { 54, 0 }, box = { 0, 0, 72, 245 }, slot = function(k) if k < 7 then return 0, 35 * k end return 35, 35 * (k - 7) end },
    { root = { 34, 526 }, p1 = { 1, 507, 32, 16 }, p2 = { 16, 0 }, box = { -1, 0, 36, 504 }, slot = function(k) return 0, 36 * k end },
}

function X.extraShapeOf(width, height)
    if type(width) ~= "number" or type(height) ~= "number" or width <= 0 or height <= 0 then return nil end
    local ratio = width / height
    if ratio > 8 then return 1 elseif ratio > 1 then return 2 elseif ratio > 0.125 then return 3 end
    return 4
end

-- the container and the 14 slots of a bar, found among the pieces as the game made them (at their normal size)
function X.extraPieces(id)
    local function get(number)
        local component
        pcall(function() component = ui.Interfaces:GetComponent(id, number) end)
        return component
    end
    local box
    for number = 3, 40 do
        local c = get(number)
        local w, h = c and try(c, "width"), c and try(c, "height")
        if type(w) == "number" and type(h) == "number" and ((w >= 480 and w <= 600 and h <= 40) or (h >= 480 and h <= 600 and w <= 40) or (w >= 240 and w <= 265 and h >= 70 and h <= 74)
            or (h >= 240 and h <= 265 and w >= 70 and w <= 74)) then box = number; break end
    end
    if not box then return nil, "no container" end
    local slots = {}
    for number = box + 1, 400 do
        local c = get(number)
        if c then
            local w, h = try(c, "width"), try(c, "height")
            if w == 36 and h == 36 then
                slots[#slots + 1] = number
            end
        end
    end
    -- (the pieces inside a slot are 36x36 at 0,0 too: the slots are the ones that sit on the grid, plus the first one after the container)
    local heads = { box + 1 }
    for _, number in ipairs(slots) do
        local c = get(number)
        local x, y = try(c, "x"), try(c, "y")
        if number ~= box + 1 and type(x) == "number" and type(y) == "number" and not (x == 0 and y == 0) and (x % 35 == 0 or x % 36 == 0 or x % 37 == 0 or x == 35 or y % 35 == 0 or y % 36 == 0 or y % 37 == 0) then
            heads[#heads + 1] = number
        end
    end
    return box, heads
end

-- With the preset selector and the settings icon both hidden, the strip they and the scroller piece (1) take at the end of the bar is given to the
-- container, and the 14 slots are spread over the longer length.
function X.otherBoth(id) return Engine.getOtherHidden(id, 2) and Engine.getOtherHidden(id, 4) end
function X.extendLayout(layout, shape)
    local copy = {}
    for k, v in pairs(layout) do copy[k] = v end
    local box, p1 = layout.box, layout.p1
    if layout == X.EXTRA_CLASSIC or shape == 1 or shape == 2 then
        local length = p1[1] + p1[3] - box[1] + (layout == X.EXTRA_CLASSIC and 10.9 or 2)      -- (classic bars are slightly wider: 10.9 more, to be checked)
        copy.box = { box[1], box[2], length, box[4] }
        if layout == X.EXTRA_CLASSIC or shape == 1 then
            copy.slot = function(k) return math.floor(k * length / 14 + 0.5), 0 end
        else
            copy.slot = function(k)
                local x = math.floor((k % 7) * length / 7 + 0.5)
                if k < 7 then return x, 0 end
                return x, 35
            end
        end
    else
        local length = p1[2] + p1[4] - box[2] + 2      -- (two pixels more)
        copy.box = { box[1], box[2], box[3], length }
        if shape == 4 then
            copy.slot = function(k) return 0, math.floor(k * length / 14 + 0.5) end
        else
            copy.slot = function(k)
                local y = math.floor((k % 7) * length / 7 + 0.5)
                if k < 7 then return 0, y end
                return 35, y
            end
        end
    end
    return copy
end

function X.rebuildExtra(id, shape)
    local set = sets[id]
    if not set or not set.held or #set.held == 0 then return false end
    local layout = X.classicMode and X.EXTRA_CLASSIC or X.EXTRA_SHAPES[shape]
    if not layout then return false end
    if X.otherBoth(id) then layout = X.extendLayout(layout, shape) end
    X.extraShape = X.extraShape or {}
    if X.extraShape[id] then X.extraShape[id].otherDone = X.otherBoth(id) and true or false end
    X.rebuilding = true
    local count = X.unscaleForResize(set)
    local box, heads = X.extraPieces(id)
    -- (the slots of a bar spread over a longer container are not on the grid the search expects: the ones found at the normal length are used)
    X.extraCache = X.extraCache or {}
    if box and type(heads) == "table" and #heads == 14 then X.extraCache[id] = { box, heads }
    elseif X.extraCache[id] then box, heads = X.extraCache[id][1], X.extraCache[id][2] end
    if not box or #heads ~= 14 then
        X.rebuilding = false
        return false
    end
    local function put(number, values)
        local c
        pcall(function() c = ui.Interfaces:GetComponent(id, number) end)
        if not c then return end
        for field, value in pairs(values) do
            if try(c, field) ~= value then setProperty(c, field, value); count = count + 1 end
        end
    end
    put(0, { width = layout.root[1], height = layout.root[2] })
    put(1, { x = layout.p1[1], y = layout.p1[2], width = layout.p1[3], height = layout.p1[4] })
    put(2, { x = layout.p2[1], y = layout.p2[2] })
    put(box, { x = layout.box[1], y = layout.box[2], width = layout.box[3], height = layout.box[4] })
    for k, number in ipairs(heads) do
        local x, y = layout.slot(k - 1)
        put(number, { x = x, y = y })
    end
    -- (the window and its frames are put to the new shape's own size first: they are scaled from the size they have when the bar is scaled again,
    -- and at that moment they can be at the scaled size already (the window flips between the two), which scaled them twice)
    do
        local window
        for _, entry in ipairs(X.EXTRA_SHAPE_BARS) do if entry[1] == id then window = entry[2] end end
        if window then
            for offset = 0, 4 do
                local c
                pcall(function() c = ui.Interfaces:GetComponent(1477, window + offset) end)
                if c then
                    local w, h = layout.root[1] + (offset % 2 == 0 and 4 or 0), layout.root[2] + (offset % 2 == 0 and 4 or 0)
                    if try(c, "width") ~= w or try(c, "height") ~= h then
                        setProperty(c, "width", w); setProperty(c, "height", h)
                        count = count + 1
                    end
                end
            end
        end
    end
    for key, item in pairs(parentItem) do
        if item.owner == id then parentBase[key] = nil end
    end
    forgetSet(id)
    local ok, scaled = pcall(scaleInterface, id, percent)
    layoutVersion = layoutVersion + 1
    structVersion = structVersion + 1
    busyVersion = busyVersion + 1
    forceFrames = math.max(forceFrames, FORCE_FRAMES)
    if ok and scaled and sets[id] then sets[id].posReady = true end
    if afterFrameHook then pcall(afterFrameHook) end
    X.rebuilding = false
    pcall(X.fixSlotBackgrounds, id)
    return true
end

-- called every few frames: has a bar's window taken another shape, and has it stayed that way for a moment?
-- the main bar to a frame size (its own shape, or the classic one): the frames 1477:72, 73 and 69 are put to the size that goes with it first, so
-- they are scaled from it and not from whatever size they have at that moment (see rebuildExtra)
-- The minimise button (a 12x12 child of 1477:73) sits 14 in from the frame's right edge, 2 down (728 in a 742 frame). The game puts it there when
-- it lays the bar out; after a frame was resized here it stayed where the old frame's edge was (far left in classic).
function X.setWindowTarget(number, height)
    local key = "1477:" .. number
    local set = sets[1430]
    if not set or not set.held then return end
    for _, item in ipairs(set.held) do
        if item.frameKey == key and item.target then
            item.target.height = height
            if item.home and item.home.height then item.home.height = height end
        end
    end
end

function X.fixMinimise()
    local frame, button
    pcall(function() frame = ui.Interfaces:GetComponent(1477, 73) end)
    if not frame then return end
    -- (the frame 1477:73 and the window 1477:69 around the main bar stayed at the unscaled size after a rebuild, 552x76 at 120 percent with the
    -- bar scaled inside it; they are put to the scaled size of the frame the bar was given)
    if X.mainFrame then
        local wantedW, wantedH = math.floor(X.mainFrame[1] * percent / 100 + 0.5), math.floor(X.mainFrame[2] * percent / 100 + 0.5)
        -- (the height is the inner frame's own plus the 4 border: with two rows that frame is taller than the one row this was worked out from,
        -- and the two were set against each other every frame)
        do
            local inner
            pcall(function() inner = try(ui.Interfaces:GetComponent(1477, 72), "height") end)
            if type(inner) == "number" and inner > 0 and not (X.holdPaused or X.layoutChangedAt or X.rebuilding) then wantedH = inner + 4 end
        end
        for _, number in ipairs({ 73, 69 }) do
            local c
            pcall(function() c = ui.Interfaces:GetComponent(1477, number) end)
            if c and (math.abs((try(c, "width") or 0) - wantedW) > 1 or math.abs((try(c, "height") or 0) - wantedH) > 1) then
                setProperty(c, "width", wantedW); setProperty(c, "height", wantedH)
                if (X.frameLines or 0) < 6 then
                    X.frameLines = (X.frameLines or 0) + 1
                end
            end
        end
    end
    local width = try(frame, "width")
    if type(width) ~= "number" or width <= 0 then return end
    pcall(function()
        frame:IterateDynamicComponents(function(child)
            if try(child, "width") == 12 and try(child, "height") == 12 then button = child end
        end)
    end)
    if not button then return end
    local wanted = width - 14
    if (X.minimiseReads or 0) < 6 then
        X.minimiseReads = (X.minimiseReads or 0) + 1
    end
    if try(button, "x") ~= wanted then
        setProperty(button, "x", wanted)
        if (X.minimiseLines or 0) < 10 then
            X.minimiseLines = (X.minimiseLines or 0) + 1
        end
    end
    if try(button, "y") ~= 2 then setProperty(button, "y", 2) end
end

function X.rebuildMainTo(width, height)
    local set = sets[1430]
    if not set or not set.held or #set.held == 0 or X.isHiddenBar(1430) then return false end
    for _, entry in ipairs({ { 72, 0 }, { 73, 4 }, { 69, 4 } }) do
        local c
        pcall(function() c = ui.Interfaces:GetComponent(1477, entry[1]) end)
        if c and (try(c, "width") ~= width + entry[2] or try(c, "height") ~= height + entry[2]) then
            setProperty(c, "width", width + entry[2]); setProperty(c, "height", height + entry[2])
        end
    end
    X.rebuildShape(set, width, height)
    X.mainFrame = { width + 4, height + 4 }
    X.minimiseUntil = (X.drawCount or 0) + 150
    return true
end

-- the shape of the main bar from the proportions of its window (the same at any size)
function X.mainShapeFromWindow()
    local c
    pcall(function() c = ui.Interfaces:GetComponent(1477, 69) end)
    local w, h = c and try(c, "width"), c and try(c, "height")
    if type(w) ~= "number" or type(h) ~= "number" or h <= 0 then return nil end
    local ratio = w / h
    if ratio > 4 then return 1 elseif ratio > 1 then return 2 elseif ratio > 0.3 then return 3 end
    return 4
end

-- A bar's pieces written by the game for a new shape are placed from the size the buttons have at that moment: held at their scaled size they
-- gave every piece inside a button a wrong place, and taken as the game's own that stayed (the button backgrounds chopped up). As with the
-- main bar, the moment the game lays a bar out (its root takes one of the shapes' own sizes, which is not the size held), the bar is put
-- back to its normal size and held no more, so that the pieces the game writes next are placed against that. It is scaled again when the
-- shape has settled (extraShapeStep).
X.EXTRA_ROOTS = { { 526, 34 }, { 261, 72 }, { 72, 261 }, { 34, 526 }, { 548, 34 } }
function X.extraEarly()
    if X.rebuilding or X.holdPaused or X.layoutChangedAt or X.startRescaleAt or X.resizing or X.classicMode or percent <= 100 then return end
    X.extraShape = X.extraShape or {}
    for _, entry in ipairs(X.EXTRA_SHAPE_BARS) do
        local id = entry[1]
        local set = sets[id]
        if set and set.held and #set.held > 0 and not set.paused and not X.isHiddenBar(id) then
            local root
            pcall(function() root = ui.Interfaces:GetComponent(id, 0) end)
            local w, h = root and try(root, "width"), root and try(root, "height")
            if type(w) == "number" and type(h) == "number" then
                if not set.rootItem or set.rootFor ~= #set.held then
                    set.rootItem, set.rootFor = nil, #set.held
                    for _, item in ipairs(set.held) do
                        if item.component and keyOf(item.component) == id .. ":0" then set.rootItem = item; break end
                    end
                end
                local item = set.rootItem
                local target = item and item.target
                if target and type(target.width) == "number" and type(target.height) == "number"
                    and (math.abs(w - target.width) > 2 or math.abs(h - target.height) > 2) then
                    for _, native in ipairs(X.EXTRA_ROOTS) do
                        if math.abs(w - native[1]) <= 1 and math.abs(h - native[2]) <= 1 then
                            local state = X.extraShape[id]
                            if not state then state = { applied = 0, seen = 0, since = X.drawCount or 0 }; X.extraShape[id] = state end
                            local count = X.unscaleForResize(set)
                            set.paused = true
                            state.pausedAt = X.drawCount or 0
                            state.seen, state.since = 0, X.drawCount or 0
                            break
                        end
                    end
                end
            end
        end
    end
end

-- The main bar with the preset selector and the settings icon both hidden: the action bar layer (61) takes the strip at the end of the bar (where the
-- scroller piece 254 is) and the 14 slots (the first stays at 0,0; slot k is piece 62 + 13 * k) are spread over the longer length.
function X.mainExtended(number, index, values)
    local p1 = X.SHAPE_PIECES[254] and X.SHAPE_PIECES[254][index]
    if not p1 then return values end
    local along = (index == 3 or index == 4) and p1[2] + p1[4] or p1[1] + p1[3]
    local length = along + (index == 5 and 10.9 or 2)
    if number == 61 then
        if index == 3 then return { values[1], values[2], values[3], length } end
        if index == 4 then return { values[1], values[2], values[3], length } end
        return { values[1], values[2], length, values[4] }
    end
    if number >= 75 and number <= 231 and (number - 62) % 13 == 0 then
        local k = (number - 62) // 13
        local a, b = values[1], values[2]
        if index == 1 or index == 5 then a = math.floor(k * length / 14 + 0.5)
        elseif index == 4 then b = math.floor(k * length / 14 + 0.5)
        elseif index == 2 then a, b = math.floor((k % 7) * length / 7 + 0.5), (k // 7) * 35
        elseif index == 3 then a, b = (k // 7) * 35, math.floor((k % 7) * length / 7 + 0.5) end
        return { a, b, values[3], values[4] }
    end
    return values
end

-- the main bar is laid out again when the two boxes were changed (or at start, when both are on)
function X.mainOtherStep()
    if not X.mainOtherDirty then return end
    local set = sets[1430]
    if not set or not set.held or #set.held == 0 or set.paused or X.isHiddenBar(1430) then return end
    if X.rebuilding or X.resizing or (DragFix.boxVisible and DragFix.boxVisible()) then return end
    X.mainOtherDirty = false
    X.mainOtherLaid = X.otherBoth(1430) and true or false
    -- (only the layer and the slots are changed, in the sizes the bar was scaled from and in what is held, so the status bars and the
    -- rest of the bar are not touched)
    local index = X.classicMode and 5 or (X.shapeIndex or 1)
    local both = X.otherBoth(1430)
    local found, changed = 0, 0
    for _, item in ipairs(set.held) do
        local component = item.component
        local number = component and not item.frame and not item.owner and tonumber(string.match(tostring(keyOf(component) or ""), "^1430:(%d+)$"))
        if number and (number == 61 or (number >= 75 and number <= 231 and (number - 62) % 13 == 0)) then
            found = found + 1
            local row = X.SHAPE_PIECES[number]
            local normal = row and row[index]
            local base = normal and set.originals[component]
            if base then
                local wanted = both and X.mainExtended(number, index, normal) or normal
                -- (what has been added to the scaled values since, such as the second row's height and the layer sitting one row lower, is kept:
                -- only the difference between the old and the new sizes is applied)
                local function scaledOf(field, value)
                    if type(value) ~= "number" then return value end
                    if (field == "x" or field == "y") and math.abs(value) <= SMALL_OFFSET then return value end
                    return math.floor(value * percent / 100 + 0.5)
                end
                local old = { x = base.x, y = base.y, width = base.width, height = base.height }
                base.x, base.y, base.width, base.height = wanted[1], wanted[2], wanted[3], wanted[4]
                if type(item.target) == "table" then
                    for _, field in ipairs({ "x", "y", "width", "height" }) do
                        if type(item.target[field]) == "number" and type(old[field]) == "number" and type(base[field]) == "number" then
                            local extra = item.target[field] - scaledOf(field, old[field])
                            local value = scaledOf(field, base[field]) + extra
                            if value ~= item.target[field] then
                                item.target[field] = value
                                setProperty(component, field, value)
                            end
                        end
                    end
                    changed = changed + 1
                end
            end
        end
    end
    layoutVersion = layoutVersion + 1
    X.otherBumps = (X.otherBumps or 0) + 1
end

function X.extraShapeStep()
    if X.rebuilding or X.holdPaused or X.layoutChangedAt or X.startRescaleAt or X.resizing then return end
    X.mainOtherStep()
    if X.minimiseUntil and (X.drawCount or 0) <= X.minimiseUntil then pcall(X.fixMinimise) end
    X.extraShape = X.extraShape or {}
    if X.classicMode then
        -- (classic: bars 1 to 3 are put into their 1x14 layouts, once; the game lays them out too but the shapes held here stayed over it)
        if not X.mainClassicDone and sets[1430] and sets[1430].held and #sets[1430].held > 0 then
            X.mainClassicDone = true
            X.mainOtherLaid = false; if X.otherBoth(1430) then X.mainOtherDirty = true end
            if X.mainHandledMode == "classic" then return end
            -- (the game lays classic out itself; only a bar that was not 1x14 needs putting there. A bar that was 1x14 is left as it is: rebuilding
            -- it moved the minimise button and lost the centring of the bars' text)
            if not (X.preClassic and X.preClassic.started) then pcall(X.rebuildMainTo, 548, 72) end
            return
        end
        for _, entry in ipairs(X.EXTRA_SHAPE_BARS) do
            local id = entry[1]
            local set = sets[id]
            local state = X.extraShape[id]
            if not state then state = { applied = 0, seen = 1, since = X.drawCount or 0 }; X.extraShape[id] = state end
            if not state.classicDone and set and set.held and #set.held > 0 and not X.isHiddenBar(id) then
                state.classicDone = true
                if not (X.preClassic and X.preClassic.started) then
                    pcall(X.rebuildExtra, id, 1)
                    return
                end
            end
            -- (the two Other Settings boxes were changed while in classic: the bar is laid out again, longer or as it was)
            if state.classicDone and set and set.held and #set.held > 0 and not set.paused and not X.isHiddenBar(id)
                and (state.otherDone or false) ~= (X.otherBoth(id) and true or false)
                and not (DragFix.boxVisible and DragFix.boxVisible()) then
                pcall(X.rebuildExtra, id, 1)
                return
            end
            -- (coming back to modern, whatever shape the window has is laid out)
            state.applied, state.seen, state.since = 0, 0, X.drawCount or 0
        end
        return
    end
    if X.mainClassicDone then
        X.mainClassicDone = false
        X.mainOtherLaid = false; if X.otherBoth(1430) then X.mainOtherDirty = true end
        if X.mainHandledMode == "modern" then X.mainHandledMode = nil; return end
        X.mainHandledMode = nil
        local shape = X.preClassic and X.preClassic.main
        if (not shape or shape == 1) and X.leaveSeen and X.leaveSeen.main then shape = X.leaveSeen.main end
        if not shape or shape == 1 then shape = X.mainShapeFromWindow() or 1 end
        X.shapeIndex = shape
        if Engine.shapeCallback then pcall(Engine.shapeCallback, shape) end
        local frame = X.BAR_SHAPES[shape]
        if frame and shape ~= 1 then pcall(X.rebuildMainTo, frame[1], frame[2]) end
        return
    end
    for _, state in pairs(X.extraShape) do state.classicDone = false end
    if X.preClassic then
        -- (back from classic: every bar goes back to the shape it had before)
        local pending = false
        for _, entry in ipairs(X.EXTRA_SHAPE_BARS) do
            local id = entry[1]
            local set = sets[id]
            if not X.preClassic.done[id] and set and set.held and #set.held > 0 and not X.isHiddenBar(id) then
                -- (a bar that was rebuilt for classic has lost its window's shape: the shape it had is given back. One that was left to the
                -- game, or that was not known (the plugin started in classic), is read from its window, which the game has laid out again)
                local shape = X.preClassic.extras[id]
                if (not shape or shape == 1) and X.leaveSeen and X.leaveSeen.extras[id] then shape = X.leaveSeen.extras[id] end
                if not shape or shape == 1 then
                    local window
                    for _, entry in ipairs(X.EXTRA_SHAPE_BARS) do if entry[1] == id then window = entry[2] end end
                    local c
                    if window then pcall(function() c = ui.Interfaces:GetComponent(1477, window) end) end
                    shape = c and X.extraShapeOf(try(c, "width"), try(c, "height")) or 1
                end
                X.preClassic.done[id] = true
                local state = X.extraShape[id]
                if not state then state = {}; X.extraShape[id] = state end
                state.applied, state.seen, state.since = shape, shape, X.drawCount or 0
                -- (always, 1x14 too: the classic bars are wider, and the modern width is put back by this)
                pcall(X.rebuildExtra, id, shape)
                return
            end
        end
        X.preClassic = nil
    end
    for _, entry in ipairs(X.EXTRA_SHAPE_BARS) do
        local id, window = entry[1], entry[2]
        local set = sets[id]
        local state = X.extraShape[id]
        if set and set.held and #set.held > 0 and (not set.paused or (state and state.pausedAt)) and not X.isHiddenBar(id) then
            local component
            pcall(function() component = ui.Interfaces:GetComponent(1477, window) end)
            local shape = component and X.extraShapeOf(try(component, "width"), try(component, "height"))
            if shape then
                if not state then
                    X.extraShape[id] = { applied = shape, seen = shape, since = X.drawCount or 0 }
                elseif state.seen ~= shape then
                    state.seen, state.since = shape, X.drawCount or 0
                elseif state.applied ~= shape and (X.drawCount or 0) - state.since >= 20 and not (DragFix.boxVisible and DragFix.boxVisible()) then
                    state.applied, state.pausedAt = shape, nil
                    pcall(X.rebuildExtra, id, shape)
                elseif not state.pausedAt and state.applied == shape and (state.otherDone or false) ~= (X.otherBoth(id) and true or false)
                    and not set.paused and not (DragFix.boxVisible and DragFix.boxVisible()) then
                    state.otherDone = X.otherBoth(id) and true or false
                    pcall(X.rebuildExtra, id, shape)
                elseif state.pausedAt and (X.drawCount or 0) - state.pausedAt >= 90 and not (DragFix.boxVisible and DragFix.boxVisible()) then
                    -- (laid out by the game without a change of shape: scaled again as it is)
                    state.pausedAt = nil
                    pcall(X.rebuildExtra, id, shape)
                end
            end
        end
    end
end

function X.resizeStep(set)
    if not set.paused then X.resizing = false; return end        -- (the bar was scaled again by something else)
    local item = X.shapeFrame(set)
    if not item then return end
    local width, height = try(item.component, "width"), try(item.component, "height")
    if type(width) ~= "number" or type(height) ~= "number" then return end
    local size = width .. "x" .. height
    local fingerprint = X.resizeFingerprint(set)
    local tick = X.logicCount or 0
    if size ~= X.resizeSize or fingerprint ~= X.resizeFp then X.resizeSize, X.resizeFp, X.resizeAt = size, fingerprint, tick end
    -- (scaled again once nothing has moved for a while and the button has been let go; after a long wait whatever the state)
    local quiet = tick - X.resizeAt
    local held = DragFix.boxVisible and DragFix.boxVisible() or false
    if (quiet >= 25 and not held) or quiet >= 300 then
        X.rebuildShape(set, width, height)
        X.mainHandledMode = width >= 540 and "classic" or "modern"
        if width >= 540 then X.minimiseUntil = (X.drawCount or 0) + 150; X.mainFrame = { width + 4, height + 4 } end
    end
end

-- called first in every game event, before anything is put back
function X.shapeProbe()
    if X.rebuilding or X.holdPaused or X.layoutChangedAt then return end
    local set = sets[1430]
    if not set then return end
    if X.resizing then X.resizeStep(set); return end
    local item = X.shapeFrame(set)
    if not item then return end
    local width, height = try(item.component, "width"), try(item.component, "height")
    if type(width) ~= "number" or type(height) ~= "number" then return end
    local seen = item.seen
    if type(seen) == "table" and type(seen.width) == "number" and type(seen.height) == "number"
        and math.abs(width - seen.width) <= 1 and math.abs(height - seen.height) <= 1 then return end      -- the size this plugin set
    local base = item.trueBase or item.base
    if type(base) ~= "table" or type(base.width) ~= "number" then return end
    if math.abs(width - base.width) <= 2 and math.abs(height - base.height) <= 2 then return end            -- the shape it has already
    for index, shape in ipairs(X.BAR_SHAPES) do
        -- (going into classic from a shape other than 1x14, or out of it into one: the game lays the bar out as it does for a shape, writing every
        -- piece (the status bars' too), so it is handled like a shape change. Between 1x14 and classic the mode change below does it.)
        if math.abs(width - shape[1]) <= 2 and math.abs(height - shape[2]) <= 2 and not (index == 1 and X.classicMode) then
            X.startResize(set, width, height)
            return
        end
    end
    -- (resized while minimised: the frame has the minimised size of another shape)
    if not X.classicMode then
        for index, shape in ipairs(X.COLLAPSED_SHAPES) do
            if index ~= (X.shapeIndex or 1) and math.abs(width - shape[1]) <= 2 and math.abs(height - shape[2]) <= 2 then
                X.startResize(set, width, height)
                return
            end
        end
    end
    if not X.classicMode and (X.shapeIndex or 1) ~= 1 and math.abs(width - 548) <= 2 and math.abs(height - 72) <= 2 then
        X.startResize(set, width, height)
        return
    end
end

----------------------------------------------------------------
-- WHERE THE BAR SITS
----------------------------------------------------------------
-- The game puts the bar back where it was dragged when the client starts, but it works that out from the normal size, and the bar is
-- bigger than that by the time it is scaled, so it came back in the wrong place. So where the frames above the bars sit is saved
-- (while a size above 100% is in use) and put back after the bars have been scaled at start.
local POS_OFFSET = 100000            -- PersistentDB holds whole numbers; this keeps negative positions safe

local function posKey(frameKey, axis) return "pos_" .. frameKey:gsub(":", "_") .. "_" .. axis end

local function restorePositions(set)
    for _, item in ipairs(set.held) do
        if item.frameKey then
            local x, y = Settings.get(posKey(item.frameKey, "x"), nil), Settings.get(posKey(item.frameKey, "y"), nil)
            if x and y then
                pcall(function() item.component:SetX(x - POS_OFFSET); item.component:SetY(y - POS_OFFSET) end)
            end
        end
    end
    set.posReady = true
end

local POS_STABLE_PASSES = 5        -- a place is only saved once it has stayed the same for this many looks (the game moves things around while a bar is hidden)

local function savePositions(set)
    if not set.posReady then return end
    set.lastPos = set.lastPos or {}
    set.posPending = set.posPending or {}
    for _, item in ipairs(set.held) do
        if item.frameKey then
            local x, y = try(item.component, "x"), try(item.component, "y")
            local last = set.lastPos[item.frameKey]
            if type(x) == "number" and type(y) == "number" then
                if last and last.x == x and last.y == y then
                    set.posPending[item.frameKey] = nil
                else
                    local pending = set.posPending[item.frameKey]
                    if pending and pending.x == x and pending.y == y then
                        pending.count = pending.count + 1
                    else
                        pending = { x = x, y = y, count = 1 }
                        set.posPending[item.frameKey] = pending
                    end
                    if pending.count >= POS_STABLE_PASSES then
                        set.lastPos[item.frameKey] = { x = x, y = y }
                        set.posPending[item.frameKey] = nil
                        Settings.set(posKey(item.frameKey, "x"), x + POS_OFFSET)
                        Settings.set(posKey(item.frameKey, "y"), y + POS_OFFSET)
                    end
                end
            end
        end
    end
end

----------------------------------------------------------------
-- HIDING THE BUTTON BACKGROUNDS
-- Every TOPLEVEL_V2_COMBAT_BAR__BUTTON_HOLDER_BG_<number> component is hidden while the option is on. The game shows them again
-- at times, so they are checked every few updates; the ones this hid are shown again when the option is turned off.
----------------------------------------------------------------
local HOLDER_PATTERN = "HOLDER_BG"      -- any name with HOLDER_BG in it, on any interface (the other bars may name theirs differently)
local HIDE_CHECK_EVERY = 2               -- game updates between checks while the backgrounds are hidden
local hideBackgrounds = false
local holderNames = {}
local holderIds = nil                    -- the id of every holder background, found once
local hiddenByUs = {}                    -- id -> true for the ones this has hidden
local hideTicks = 0

local function findHolderIds()
    if holderIds then return holderIds end
    holderIds = {}
    local seen = {}
    holderNames = {}
    local function add(name, value)
        name = tostring(name)
        if seen[name] or not name:find(HOLDER_PATTERN, 1, true) then return end
        value = tonumber(tostring(value))
        if value and value >= 0 then seen[name] = true; holderIds[#holderIds + 1] = value; holderNames[#holderNames + 1] = name .. "=" .. tostring(value) end
    end
    -- the keys may not be plain Lua strings, so each one is wrapped with tostring
    pcall(function() for key, value in pairs(id.Component) do add(key, value) end end)
    -- by name as well, in case the table can't be walked (a name that does not exist reads as -1). The first bar is
    -- TOPLEVEL_V2_COMBAT_BAR, the others TOPLEVEL_V2_COMBAT_BAR2, BAR3 and so on
    for bar = 1, 8 do
        local prefix = "TOPLEVEL_V2_COMBAT_BAR" .. (bar > 1 and tostring(bar) or "") .. "__BUTTON_HOLDER_BG_"
        for n = 0, 40 do
            local name = prefix .. n
            if not seen[name] then
                local ok, value = pcall(function() return id.Component[name] end)
                if ok and value ~= nil then add(name, value) end
            end
        end
    end
    return holderIds
end

local function applyHolders(hidden, report)
    local found, reached, changed, first = 0, 0, 0, nil
    X.holderCache = X.holderCache or {}
    for _, holder in ipairs(findHolderIds()) do
        found = found + 1
        -- (the component is kept from one call to the next, as this is called on every frame: it is looked for again only when it reads
        -- nothing, because the game made it again or the interface is gone)
        local component = X.holderCache[holder]
        if not component or try(component, "hidden") == nil then
            local ok, got = pcall(function() return ui.Interfaces:GetComponent(holder) end)
            component = ok and got or false
            X.holderCache[holder] = component
        end
        if component then
            reached = reached + 1
            if hidden then
                if try(component, "hidden") ~= true then
                    local set, err = pcall(function() component.hidden = true end)
                    if set then changed = changed + 1 elseif not first then first = tostring(err) end
                end
                hiddenByUs[holder] = true
            elseif hiddenByUs[holder] then
                pcall(function() component.hidden = false end)
            end
        end
    end
    if not hidden then hiddenByUs = {} end
    if report and first then
    end
end

----------------------------------------------------------------
-- HIDING THE ACTION WINDOW BACKGROUND AND BORDER
-- The action bars sit in windows named ACTION_WINDOW, ACTION_WINDOW_2 ... each with an _BACKGROUND and a _BORDER part. The exact
-- component names are not known (GUESS), so a few likely spellings are tried and the ones that exist are printed once.
----------------------------------------------------------------
local FRAME_PREFIXES = { "TOPLEVEL_V2__", "TOPLEVEL_V2_", "" }
local FRAME_PARTS = { "BACKGROUND", "BORDER" }
local hideFrames = false                 -- true while either part is being hidden
local hideParts = { BACKGROUND = false, BORDER = false }
local frameIds = nil                     -- { { name, value, part } } found once
local framesHiddenByUs = {}              -- value -> true

local function findFrameIds()
    if frameIds then return frameIds end
    frameIds = {}
    local seen = {}
    local function add(name, value)
        name = tostring(name)
        value = tonumber(tostring(value))
        if seen[name] or not value or value < 0 then return end
        seen[name] = true
        frameIds[#frameIds + 1] = { name = name, value = value, part = name:find("_BORDER", 1, true) and "BORDER" or "BACKGROUND" }
    end
    pcall(function()
        for key, value in pairs(id.Component) do
            local name = tostring(key)
            if name:find("ACTION_WINDOW", 1, true) and (name:find("_BACKGROUND", 1, true) or name:find("_BORDER", 1, true)) then add(name, value) end
        end
    end)
    for _, prefix in ipairs(FRAME_PREFIXES) do
        for n = 1, 12 do
            -- as the Dev Tools tree shows them: ACTION_WINDOW_BACKGROUND, ACTION_WINDOW_BACKGROUND_2 ... (the number goes at the end)
            for _, part in ipairs(FRAME_PARTS) do
                local name = prefix .. "ACTION_WINDOW_" .. part .. (n > 1 and ("_" .. n) or "")
                if not seen[name] then
                    local ok, value = pcall(function() return id.Component[name] end)
                    if ok and value ~= nil then add(name, value) end
                end
            end
        end
    end
    local names = {}
    for _, entry in ipairs(frameIds) do names[#names + 1] = entry.name end
    return frameIds
end

-- each part is hidden or shown according to hideParts; `restoreAll` shows everything this hid
-- FILL: instead of being hidden, the window backgrounds can be coloured (the gaps between the ability slots then show that colour).
-- GUESS: that the background piece takes `colour`/`alpha` (the game's sprites did in a test); a bright colour may come out muted if its
-- picture is dark. It takes the place of hiding the background while on.
local frameFill = nil                    -- { r, g, b, a } or nil
local framesFilled = {}                  -- value -> { colour, alpha, hidden } before it was filled
local reportedFill = false

-- Each bar's background is cut down to just its ability slots while it is coloured (the main bar's also sits behind the health,
-- prayer, adrenaline and summoning bars), and put back after. Which slots belong to a background is found by which slot tiles lie
-- inside it, once, before it is cut down. GUESS: that x, y, width and height of a background can be written; its place is corrected
-- by reading where it ends up on the screen.
local allTiles, regionChecks, lastTileScan = nil, 0, -1000
local TILE_INTERFACES = { 1430, 1670, 1671, 1672, 1673 }

local function scanTiles()
    allTiles = {}
    for _, interfaceID in ipairs(TILE_INTERFACES) do
        for _, part in ipairs(Engine.statics(interfaceID)) do
            if try(part.component, "spriteID") == 14710 then allTiles[#allTiles + 1] = part.component end
        end
    end
    lastTileScan = regionChecks
end

-- the slot tiles whose middle lies inside the background as it is now
local function tilesInside(component)
    local global, width, height = try(component, "xyGlobal"), try(component, "width"), try(component, "height")
    local found = {}
    if not (global and type(width) == "number" and type(height) == "number") then return found end
    for _, tile in ipairs(allTiles or {}) do
        local g, w, h = try(tile, "xyGlobal"), try(tile, "width"), try(tile, "height")
        if g and type(w) == "number" and type(h) == "number" then
            local cx, cy = g.x + w / 2, g.y + h / 2
            if cx >= global.x and cx <= global.x + width and cy >= global.y and cy <= global.y + height then found[#found + 1] = tile end
        end
    end
    return found
end

-- the area the background's own slot tiles cover (nil if none of them are showing)
local function abilityRegion(state, component)
    regionChecks = regionChecks + 1
    if not allTiles or regionChecks - lastTileScan >= 300 then scanTiles() end
    if not state.tiles or #state.tiles == 0 then
        -- (not assigned yet, or the tiles were not there: tried again, but not on every check, as the scan is slow)
        if regionChecks - lastTileScan >= 30 then scanTiles() end
        state.tiles = tilesInside(component)
    end
    local left, top, right, bottom
    for _, tile in ipairs(state.tiles) do
        local global, width, height = try(tile, "xyGlobal"), try(tile, "width"), try(tile, "height")
        if global and type(width) == "number" and type(height) == "number" and try(tile, "hidden") ~= true and try(tile, "visibleGlobal") ~= false then
            left = math.min(left or global.x, global.x)
            top = math.min(top or global.y, global.y)
            right = math.max(right or (global.x + width), global.x + width)
            bottom = math.max(bottom or (global.y + height), global.y + height)
        end
    end
    if not left then return nil end
    return left - 3, top - 3, right - left + 6, bottom - top + 6
end

local function fitToAbilities(component, state)
    local left, top, width, height = abilityRegion(state, component)
    if not left then
        -- the abilities are not showing (the bar is minimised): the background is hidden rather than left over the status bars
        if try(component, "hidden") ~= true then pcall(function() component.hidden = true end) end
        return false
    end
    if try(component, "hidden") == true then pcall(function() component.hidden = false end) end
    local w, h = try(component, "width"), try(component, "height")
    if type(w) == "number" and math.abs(w - width) > 0.5 then pcall(function() component:SetWidth(math.floor(width + 0.5)) end) end
    if type(h) == "number" and math.abs(h - height) > 0.5 then pcall(function() component:SetHeight(math.floor(height + 0.5)) end) end
    local global = try(component, "xyGlobal")
    if global then
        local dx, dy = left - global.x, top - global.y
        if math.abs(dx) > 0.5 then pcall(function() component:SetX(math.floor((try(component, "x") or 0) + dx + 0.5)) end) end
        if math.abs(dy) > 0.5 then pcall(function() component:SetY(math.floor((try(component, "y") or 0) + dy + 0.5)) end) end
    end
    return true
end

local function fillFrame(entry, component)
    local r, g, b, a = frameFill[1], frameFill[2], frameFill[3], frameFill[4]
    if not framesFilled[entry.value] then
        framesFilled[entry.value] = { colour = try(component, "colour"), alpha = try(component, "alpha"), hidden = try(component, "hidden") == true and not framesHiddenByUs[entry.value],
            x = try(component, "x"), y = try(component, "y"), width = try(component, "width"), height = try(component, "height") }
        if not reportedFill then
            reportedFill = true
        end
    end
    if not fitToAbilities(component, framesFilled[entry.value]) then return end
    local cur, curAlpha = try(component, "colour"), try(component, "alpha")
    local same = cur and type(curAlpha) == "number" and math.abs(curAlpha - a) < 0.004
        and math.abs((try(cur, "x") or -1) - r) < 0.004 and math.abs((try(cur, "y") or -1) - g) < 0.004
        and math.abs((try(cur, "z") or -1) - b) < 0.004
    if same then return end
    pcall(function() component.colour = Vector4.new(r, g, b, a) end)
    pcall(function() component.alpha = a end)
end

local function unfillFrame(entry, component)
    local original = framesFilled[entry.value]
    if not original then return end
    pcall(function() component.colour = original.colour or Vector4.new(1.0, 1.0, 1.0, 1.0) end)
    if type(original.alpha) == "number" then pcall(function() component.alpha = original.alpha end) end
    -- (the main background's own place and size, if it was cut down)
    if type(original.width) == "number" then pcall(function() component:SetWidth(original.width) end) end
    if type(original.height) == "number" then pcall(function() component:SetHeight(original.height) end) end
    if type(original.x) == "number" then pcall(function() component:SetX(original.x) end) end
    if type(original.y) == "number" then pcall(function() component:SetY(original.y) end) end
    if original.hidden == true then pcall(function() component.hidden = true end) else pcall(function() component.hidden = false end) end
    framesFilled[entry.value] = nil
end

local function applyFrames(restoreAll)
    for _, entry in ipairs(findFrameIds()) do
        local ok, component = pcall(function() return ui.Interfaces:GetComponent(entry.value) end)
        if ok and component then
            local filling = frameFill and entry.part == "BACKGROUND" and not restoreAll
            if filling then
                fillFrame(entry, component)
                framesHiddenByUs[entry.value] = nil
            else
                unfillFrame(entry, component)
            end
            local wantHidden = hideParts[entry.part] and not restoreAll and not filling
            if filling then
                -- (handled above)
            elseif wantHidden then
                if try(component, "hidden") ~= true then pcall(function() component.hidden = true end) end
                framesHiddenByUs[entry.value] = true
            elseif framesHiddenByUs[entry.value] then
                pcall(function() component.hidden = false end)
                framesHiddenByUs[entry.value] = nil
            end
        end
    end
end

-- The game lays the frames the bars sit in out by whether the window's background and border are showing: with them showing, a frame is
-- 2 in from the window's corner (2,2); with them hidden it is at 0,0. It only does that when the window is laid out again (a lock or an
-- unlock), so turning "hide" on left the bars where they were until the next lock, when everything shifted 2 pixels. The frames are moved
-- when the setting is changed (and moved back when it is turned off), to where the game puts them.
local CONTENT_FRAMES = { 72, 77, 82, 87, 92 }
X.framePlaces = {}
function X.placeFrames(hidden)
    for _, number in ipairs(CONTENT_FRAMES) do
        local component
        pcall(function() component = ui.Interfaces:GetComponent(1477, number) end)
        if component then
            local x, y = try(component, "x"), try(component, "y")
            if hidden then
                if type(x) == "number" and type(y) == "number" and (x ~= 0 or y ~= 0) then
                    X.framePlaces[number] = X.framePlaces[number] or { x = x, y = y }
                    pcall(function() component:SetX(0); component:SetY(0) end)
                end
            elseif X.framePlaces[number] then
                local place = X.framePlaces[number]
                X.framePlaces[number] = nil
                pcall(function() component:SetX(place.x); component:SetY(place.y) end)
            end
        end
    end
end

function Engine.getHideFrame(part) return hideParts[part] == true end

-- part = "BACKGROUND" or "BORDER"
function Engine.setHideFrame(part, on)
    if hideParts[part] == nil then return end
    hideParts[part] = on == true
    hideFrames = hideParts.BACKGROUND or hideParts.BORDER or frameFill ~= nil
    applyFrames(false)
    pcall(X.placeFrames, hideParts.BACKGROUND and hideParts.BORDER)
end

-- colours the window backgrounds (rgba as RRGGBBAA) instead of hiding them; nil/false turns it off
-- (a hook the plugin does not use at present; kept because the frame code below handles it)
function Engine.setFrameFill(rgba)
    if rgba then
        local value = math.floor(tonumber(rgba) or 0) % 4294967296
        local a = (value % 256) / 255
        value = math.floor(value / 256)
        local b = (value % 256) / 255
        value = math.floor(value / 256)
        local g = (value % 256) / 255
        value = math.floor(value / 256)
        frameFill = { (value % 256) / 255, g, b, a }
    else
        frameFill = nil
    end
    hideFrames = hideParts.BACKGROUND or hideParts.BORDER or frameFill ~= nil
    applyFrames(false)
end
function Engine.getFrameFill() return frameFill ~= nil end

----------------------------------------------------------------
-- PUBLIC
----------------------------------------------------------------

-- hides the summoning bar and makes the other three player bars fill its space (Engine.setPercent does the scaling again from the true sizes)
local function summoningComponent()
    local ok, component = pcall(function() return ui.Interfaces:GetComponent(id.Component.TOPLEVEL_V2_COMBAT_BAR__PLAYER_SUMMONING) end)
    return ok and component or nil
end

-- the fixed parts of an interface as a list of { key = "interface:number", number, component } (for the ability borders)
function Engine.statics(interfaceID)
    local list = {}
    local ok, components, keys = pcall(interfaceComponents, interfaceID)
    if not ok or not components then return list end
    for _, component in ipairs(components) do
        if not (keys and keys[component]) then
            local name = keyOf(component)
            if name then list[#list + 1] = { key = name, number = tonumber(name:match(":(%d+)$")), component = component } end
        end
    end
    return list
end

function Engine.getTwoRows() return twoRows end

-- the player bars two by two, in two rows (the bar gets taller to make room). quiet = true at start.
function Engine.setTwoRows(on, quiet)
    on = on == true
    if on == twoRows then return end
    twoRows = on
    if on then everScaled = true end
    if quiet then return end
    Engine.setPercent(percent)
end

-- the filling bars (the coloured part of the health, prayer, adrenaline and summoning bars) as they are now, for the shine overlay:
-- a list of { key, component }, in a steady order
-- looks through the bar interface (1430) for components showing the given game sprites; wanted = { [spriteNumber] = true }.
-- Returns { [spriteNumber] = component } for the ones found (the first of each).
-- the number of a static of the main bar from its game name (PLAYER_PRAYER is the holder of the prayer bar and its round button)
function Engine.staticNumber(name) return staticOf(name, 1430) end

function Engine.findSprites(wanted)
    local found = {}
    local list = interfaceComponents(1430)
    if not list then return found end
    for _, component in ipairs(list) do
        local sprite = try(component, "spriteID")
        if wanted[sprite] and not found[sprite] then found[sprite] = component end
    end
    return found
end

-- like findSprites, but through every action bar interface and keeping every match: sprite number -> list of components
-- (one interface per call, in turn, so that no single frame has to go through all five)
local ALL_BARS = { 1430, 1670, 1671, 1672, 1673, 1477 }    -- (1477 only for the minimise button, 1477:73: looked at inside that component only, as the whole interface is large)
function Engine.findSpritesAll(wanted, which)
    local found = {}
    local interfaceID = ALL_BARS[which]
    if interfaceID == 1477 then
        local function check(component)
            local sprite = try(component, "spriteID")
            if sprite ~= nil and wanted[sprite] then
                found[sprite] = found[sprite] or {}
                table.insert(found[sprite], component)
            end
        end
        pcall(function()
            local root = ui.Interfaces:GetComponent(1477, 73)
            if not root then return end
            check(root)
            root:IterateDynamicComponents(function(child)
                check(child)
                pcall(function() child:IterateDynamicComponents(check) end)
            end)
        end)
        return found
    end
    local list = interfaceID and interfaceComponents(interfaceID)
    if list then
        for _, component in ipairs(list) do
            local sprite = try(component, "spriteID")
            if sprite ~= nil and wanted[sprite] then
                found[sprite] = found[sprite] or {}
                table.insert(found[sprite], component)
            end
        end
    end
    return found
end
Engine.ALL_BARS_COUNT = #ALL_BARS

-- The same two searches, made a few hundred components at a time over several frames, as a coroutine (the whole of one bar's interface in one
-- frame was about 2,000 reads, and a frame that did that was the one that dropped). searchStart gives a search; searchStep goes on with it and
-- returns true when it is finished; its results are then in search.found (sprite number -> component, or -> a list of them when `many`).
-- (the pieces of a component are collected inside the game's callback and visited outside it: a coroutine cannot give way inside one)
local SEARCH_SLICE = 40
function Engine.searchStart(which, wanted, many)
    local interfaceID = ALL_BARS[which or 1] or 1430
    local search = { found = {}, wanted = wanted, many = many, interfaceID = interfaceID }
    if interfaceID == 1477 then
        -- (the minimise button's own parts only: small, done in one go)
        search.found = Engine.findSpritesAll(wanted, which)
        search.finished = true
        return search
    end
    search.co = coroutine.create(function()
        local seen, visited = {}, 0
        local function visit(component)
            if not component or seen[component] then return end
            seen[component] = true
            local sprite = try(component, "spriteID")
            if sprite ~= nil and wanted[sprite] then
                if many then
                    search.found[sprite] = search.found[sprite] or {}
                    table.insert(search.found[sprite], component)
                elseif not search.found[sprite] then
                    search.found[sprite] = component
                end
            end
            visited = visited + 1
            if visited % SEARCH_SLICE == 0 then coroutine.yield() end
            local kids, statics = {}, {}
            pcall(function() component:IterateDynamicComponents(function(child) kids[#kids + 1] = child end) end)
            for _, child in ipairs(kids) do visit(child) end
            pcall(function() component:IterateStaticComponents(function(child) statics[#statics + 1] = child end) end)
            for _, child in ipairs(statics) do visit(child) end
        end
        if isLoaded(interfaceID) then
            for staticID = 0, MAX_STATIC_ID do
                local ok, component = pcall(function() return ui.Interfaces:GetComponent(interfaceID, staticID) end)
                if ok and component then visit(component) end
                if staticID % 400 == 399 then coroutine.yield() end
            end
        end
    end)
    return search
end

function Engine.searchStep(search)
    if search.finished then return true end
    local ok = coroutine.resume(search.co)
    if not ok or coroutine.status(search.co) == "dead" then search.finished = true end
    return search.finished == true
end

function Engine.fillComponents()
    local list = {}
    local kinds = {}          -- "1430:9" -> "health" ... (which bar a fill belongs to)
    for kind, name in pairs({ health = "PLAYER_HEALTH_BAR", prayer = "PLAYER_PRAYER_BAR", adrenaline = "PLAYER_ADRENALINE_BAR", summoning = "PLAYER_SUMMONING_BAR" }) do
        local number = staticOf(name, 1430)
        if number then kinds["1430:" .. number] = kind end
    end
    for _, set in pairs(sets) do
        local texts = {}      -- prefix -> the bar's text (the number shown on it)
        for _, item in ipairs(set.held) do
            if item.prefix and not item.adaptive and item.component and type(try(item.component, "content")) == "string"
                and type(try(item.component, "font")) == "number" then
                texts[item.prefix] = item.component
            end
        end
        for _, item in ipairs(set.held) do
            if item.adaptive and item.component and (item.prefix or item.key) then
                -- (full: how wide the coloured part is when the bar is full)
                local full = item.fullWidth and item.percent and item.fullWidth * item.percent / 100 or nil
                local prefix = item.prefix or item.key
                list[#list + 1] = { key = prefix, component = item.component, full = full, kind = kinds[prefix], text = texts[prefix] }
            end
        end
    end
    table.sort(list, function(a, b) return a.key < b.key end)
    return list
end

-- (a hook the plugin does not use at present; kept because the fill code reads fillGrow)
-- makes one bar's fill `width` pixels wider and `height` pixels taller than the engine would (to the right and downwards)
function Engine.setFillGrow(kind, width, height, left)
    width, height, left = tonumber(width) or 0, tonumber(height) or 0, tonumber(left) or 0
    local oldWidth = fillGrow[kind] and (fillGrow[kind].width + fillGrow[kind].left) or 0
    if width == 0 and height == 0 and left == 0 then fillGrow[kind] = nil else fillGrow[kind] = { width = width, height = height, left = left } end
    local grow = fillGrow[kind]
    local newWidth = grow and (grow.width + grow.left) or 0
    for _, set in pairs(sets) do
        for _, item in ipairs(set.held) do
            if item.adaptive and item.prefix and kindOfPrefix(item.prefix) == kind and item.target.height then
                local base = (item.target.height - (item.growH or 0))
                item.growH = grow and grow.height or 0
                item.target.height = base + item.growH
                setProperty(item.component, "height", item.target.height)
                item.seen.height = try(item.component, "height")
                -- (the width too, if the bar has any: an empty bar stays empty)
                -- (and the left edge: it moves out by the same amount as the extra left pixels)
                if type(item.target.x) == "number" then
                    item.target.x = item.target.x + (item.growL or 0) - (grow and grow.left or 0)
                    item.growL = grow and grow.left or 0
                    setProperty(item.component, "x", item.target.x)
                    item.seen.x = try(item.component, "x")
                end
                if type(item.target.width) == "number" and item.target.width > 0 and newWidth ~= oldWidth then
                    item.target.width = math.max(1, item.target.width - oldWidth + newWidth)
                    setProperty(item.component, "width", item.target.width)
                    item.seen.width = try(item.component, "width")
                end
            end
        end
    end
end

-- fits one bar's fill to the inside of its frame (see FIT_RATIO); everything is scaled again so that it takes effect (or is undone)
-- quiet = true: only the flag is set (at start, before the bars are scaled for the first time, and when shutting down); the bars are
-- laid out by the scaling that comes next, not by a second one on top of it
function Engine.setFillFit(kind, on, quiet)
    on = on == true
    if (fillFit[kind] == true) == on then return end
    fillFit[kind] = on or nil
    -- (a fitted fill is laid out by the scaling even at 100%, so the sizes are held then too, as for a thicker bar or hidden summoning:
    -- without this nothing was laid out at 100% and the fill stayed where the game puts it until the size was changed)
    if on then everScaled = true end
    if quiet then return end
    Engine.setPercent(percent)
end

function Engine.layoutVersion() return layoutVersion end
-- (like layoutVersion without the slots' overlay pieces the game makes again on every cast: for what only needs to look again when the bars really changed)
function Engine.busyVersion() return busyVersion end
function Engine.structVersion() return structVersion end
function Engine.isBusy() return forceFrames > 0 or burst > 0 end
-- true for a few frames after the slots were updated (a burst of variable updates, as an ability cast sends)
function Engine.slotsTouched() return frame <= (X.slotsTouchedUntil or -1) end
function Engine.setAfterFrame(hook) afterFrameHook = hook end

function Engine.getBarHeight() return barHeight end

-- 0 = the normal thin bars; otherwise the thickness (before scaling) of the player bars, up to the 24 the row has room for.
-- quiet = true at start: only the value is set, the bars are laid out when they are scaled.
function Engine.setBarHeight(height, quiet)
    height = math.max(0, math.min(24, math.floor((tonumber(height) or 0) + 0.5)))
    if height == barHeight then return end
    barHeight = height
    if height > 0 then everScaled = true end
    if quiet then return end
    Engine.setPercent(percent)
end

function Engine.getHideSummoning() return summoningHidden end

-- quiet = true at start: only the flag is set, the bars are laid out when they are scaled
function Engine.setHideSummoning(on, quiet)
    on = on == true
    if on == summoningHidden then return end
    summoningHidden = on
    if on then everScaled = true end           -- the sizes are held even at 100%
    if quiet and on then return end
    local component = summoningComponent()
    if component then pcall(function() component.hidden = on end) end
    if quiet then return end                   -- (shown again at once even when quiet; the layout is left to the caller)
    Engine.setPercent(percent)
end

-- "Other Settings": the preset selector (static 4) and the settings icon (static 2) of the extra bars 1670 to 1673 can be hidden one by one.
local gameIds = id               -- (the game's component names; applyOther has a parameter called id)
local otherHidden = {}          -- [interface] = { [4] = bool, [2] = bool }
function Engine.getOtherHidden(id, static) return otherHidden[id] and otherHidden[id][static] == true end
function X.applyOther(id)
    local flags = otherHidden[id]
    if not flags then return end
    for static, on in pairs(flags) do
        local c
        if id == 1430 then
            -- (the main bar's two components are found by name)
            local name = static == 4 and "BAR_INDICATOR" or "FULLSCREEN_SETTINGS_LAYER"
            local ok, value = pcall(function() return gameIds.Component["TOPLEVEL_V2_COMBAT_BAR__" .. name] end)
            value = ok and tonumber(tostring(value)) or nil
            if value and value >= 0 then pcall(function() c = ui.Interfaces:GetComponent(value // 65536, value % 65536) end) end
            X.otherNamed = X.otherNamed or {}
            if not X.otherNamed[static] then
                X.otherNamed[static] = true
            end
        else
            pcall(function() c = ui.Interfaces:GetComponent(id, static) end)
        end
        if c and try(c, "hidden") ~= on then pcall(function() c.hidden = on end) end
    end
end
function Engine.setOtherHidden(id, static, on, quiet)
    if (static ~= 2 and static ~= 4) or type(id) ~= "number" then return end
    otherHidden[id] = otherHidden[id] or {}
    otherHidden[id][static] = on == true
    if on then everScaled = true end
    if id == 1430 and (X.mainOtherLaid or false) ~= (X.otherBoth(1430) and true or false) then X.mainOtherDirty = true end
    if quiet then return end
    X.applyOther(id)
    Engine.setPercent(percent)
end
-- Hide Lock Button: the lock button (1430:268) is hidden and the player bars take its space
function Engine.getLockHidden() return lockHidden end
function X.applyLock()
    local component
    pcall(function() component = ui.Interfaces:GetComponent(1430, 268) end)
    if component and try(component, "hidden") ~= lockHidden then pcall(function() component.hidden = lockHidden end) end
end
function Engine.setLockHidden(on, quiet)
    on = on == true
    if on == lockHidden then return end
    lockHidden = on
    if on then everScaled = true end
    X.applyLock()
    if quiet then return end
    Engine.setPercent(percent)
end

-- Hide Expand Button: the minimise button (a 12x12 child of the frame 1477:73) is hidden
local expandHidden = false
function Engine.getExpandHidden() return expandHidden end
function X.applyExpand()
    local button = X.expandButton
    -- (the button found before is used on every frame; the frame is searched again when it is not the right piece any more)
    if button and not (try(button, "width") == 12 and try(button, "height") == 12) then button = nil end
    if not button then
        local frame
        pcall(function() frame = ui.Interfaces:GetComponent(1477, 73) end)
        if not frame then return end
        pcall(function()
            frame:IterateDynamicComponents(function(child)
                if try(child, "width") == 12 and try(child, "height") == 12 then button = child end
            end)
        end)
        X.expandButton = button
    end
    if button and try(button, "hidden") ~= expandHidden then pcall(function() button.hidden = expandHidden end) end
end
function Engine.setExpandHidden(on, quiet)
    on = on == true
    if on == expandHidden then return end
    expandHidden = on
    if quiet and on then return end
    X.applyExpand()
end

function Engine.getHideBackgrounds() return hideBackgrounds end


function Engine.setHideBackgrounds(on)
    hideBackgrounds = on == true
    applyHolders(hideBackgrounds, true)
end

-- the button backgrounds are kept hidden on every frame (the game shows them again when a slot updates, as on every ability cast, and
-- every second game update left them showing for several frames); called before and after the interface is drawn
function X.holdAll()
    if expandHidden then X.applyExpand() end
    if hideBackgrounds then applyHolders(true) end
end

-- called on every game update: keeps the backgrounds hidden when the game shows them again
function Engine.holdHidden()
    for id in pairs(otherHidden) do X.applyOther(id) end
    if lockHidden then X.applyLock() end
    if expandHidden then X.applyExpand() end
    if not (hideBackgrounds or summoningHidden or hideFrames) then return end
    hideTicks = hideTicks + 1
    if hideTicks % HIDE_CHECK_EVERY ~= 0 then return end
    if hideFrames then applyFrames(false) end
    if hideBackgrounds then applyHolders(true) end
    if summoningHidden then
        local component = summoningComponent()
        if component and try(component, "hidden") ~= true then pcall(function() component.hidden = true end) end
    end
end

function Engine.getPercent() return percent end

-- the size wanted (100 puts everything back). Interfaces that aren't loaded yet are scaled as soon as they are.
function Engine.setPercent(newPercent)
    X.fillGood, X.fillSeen = nil, nil
    DragFix.restoreFrames()
    -- (a new layout still being taken from the game: what the game laid out is taken first. Putting the old sizes back over it would lose
    -- it, and the bars on screen would be scaled from the old layout's places.)
    if X.holdPaused and X.layoutChangedAt and not X.layoutRescale then
        pcall(X.absorbLayout)
        X.holdPaused, X.layoutChangedAt = false, nil
        X.layoutSig, X.layoutSame, X.layoutWaitSaid = nil, 0, false
    end
    newPercent = tonumber(newPercent) or 100
    percent = math.max(100, math.min(150, math.floor(newPercent + 0.5)))
    if percent > 100 then everScaled = true end
    -- everything is put back first and then scaled from the true sizes. An interface that has not been seen on screen for a moment
    -- yet (the plugin has just started) is left to Engine.tick, so a half-built interface is not scaled.
    restoreAll()
    if percent == 100 and not everScaled then
        if afterFrameHook then pcall(afterFrameHook) end
        return
    end
    -- Going back to 100% after a bigger size: the sizes are still held (at their normal values). Putting them back once was not
    -- enough: dragging the bar afterwards made the game bring the big frame back.
    for _, id in ipairs(INTERFACES) do
        if (loadedStreak[id] or 0) >= SETTLE_CHECKS and isLoaded(id) and not X.isHiddenBar(id) then
            if scaleInterface(id, percent) and sets[id] then sets[id].posReady = true end
        end
    end
    -- anything drawn over the bars (the gradient) is moved at once, and kept up with for a few frames while the game catches up
    forceFrames = math.max(forceFrames, FORCE_FRAMES)
    if afterFrameHook then pcall(afterFrameHook) end
    pcall(X.restackClassic)
end

----------------------------------------------------------------
-- WINDOW PLACES
----------------------------------------------------------------
-- When the game window is made smaller the game moves the bars' windows to keep them on screen, and does not move them back
-- when the window returns to its size. The place of each window is remembered for every size the game window has had (looked at only
-- while the size has been steady, so a place the game has just moved it to is never taken for the player's), and put back when that size
-- comes round again.
local WINDOW_KEY = "BetterActionBars_window"
local keptPositions = {}               -- "WxH" (or "start" before any change was seen) -> { "interface:static" -> { x, y } }
local screenKey, baseKey = nil, nil    -- the current size; the first size seen (the one the saved places belong to)
local settleLeft, pendingRestore = 0, false

-- the components above an interface, outside it (the windows the player drags): { key, component }
local function windowsOf(interfaceID)
    local list = {}
    local anchor
    pcall(function() anchor = ui.Interfaces:GetComponent(interfaceID, 0) end)
    local current, level = anchor and try(anchor, "parentStatic"), 0
    while current and level < PARENT_LEVELS + 2 do
        local name = keyOf(current)
        if name and try(current, "interfaceID") ~= interfaceID then list[#list + 1] = { key = name, component = current } end
        current = try(current, "parentStatic")
        level = level + 1
    end
    return list
end

local function snapshotWindows(into)
    for _, interfaceID in ipairs(INTERFACES) do
        if isLoaded(interfaceID) then
            for _, window in ipairs(windowsOf(interfaceID)) do
                local x, y = try(window.component, "x"), try(window.component, "y")
                if type(x) == "number" and type(y) == "number" then into[window.key] = { x = x, y = y } end
            end
        end
    end
end

local windowLines = 0
local function applyWindows(saved, verbose)
    if not saved then
        if verbose and windowLines < 30 then windowLines = windowLines + 1;  end
        return
    end
    for _, interfaceID in ipairs(INTERFACES) do
        if isLoaded(interfaceID) then
            for _, window in ipairs(windowsOf(interfaceID)) do
                local place = saved[window.key]
                if verbose and windowLines < 30 then
                    windowLines = windowLines + 1
                end
                if place then pcall(function() window.component:SetX(place.x); window.component:SetY(place.y) end) end
            end
        end
    end
end

local function restoreWindows(key)
    local saved = keptPositions[key]
    if not saved then return end
    for _, interfaceID in ipairs(INTERFACES) do
        if isLoaded(interfaceID) then
            for _, window in ipairs(windowsOf(interfaceID)) do
                local place = saved[window.key]
                if place then pcall(function() window.component:SetX(place.x); window.component:SetY(place.y) end) end
            end
        end
    end
end

-- every watch pass: counts down after a size change, then puts the places back, or remembers them while nothing is changing
local function watchWindows()
    if settleLeft > 0 then
        settleLeft = settleLeft - 1
        if pendingRestore then restoreWindows(screenKey or "start") end
        if settleLeft == 0 then pendingRestore = false end
        return
    end
    if baseKey and not screenKey then return end
    local key = screenKey or "start"
    keptPositions[key] = keptPositions[key] or {}
    snapshotWindows(keptPositions[key])
end

-- The layout editor: when a confirmation popup opens (TOPLEVEL_V2_CONFIRM_POPUP_ID goes up from 0) the places of the bars are copied; when it
-- closes (back to 0) the game puts the bars at the places its own layout has, and they are put back to the copy for a little while.
function X.layoutPopup(opened, closed, why)
    if opened then
        local copy = {}
        snapshotWindows(copy)
        X.popupCopy = copy
    elseif closed and X.popupCopy and not X.classicMode then
        local key = screenKey or "start"
        keptPositions[key] = keptPositions[key] or {}
        for name, place in pairs(X.popupCopy) do keptPositions[key][name] = place end
        settleLeft, pendingRestore = 15, true
    end
end

-- After a hidden bar comes back the game can leave its settings layers (the scroller's neighbours and the bar indicator) and what is inside
-- them hidden, so they are shown again. (Each action bar has its own name prefix and sits in its own interface.)
local function showSettingsLayers()
    for bar = 1, 8 do
        local prefix = "TOPLEVEL_V2_COMBAT_BAR" .. (bar > 1 and tostring(bar) or "") .. "__"
        for _, name in ipairs({ "FULLSCREEN_SETTINGS_LAYER", "BAR_INDICATOR" }) do
            local ok, value = pcall(function() return id.Component[prefix .. name] end)
            value = ok and tonumber(tostring(value)) or nil
            local component
            if value and value >= 0 then
                pcall(function() component = ui.Interfaces:GetComponent(value // 65536, value % 65536) end)
            end
            if component then
                pcall(function() component.hidden = false end)
                local function show(parent, depth)
                    if depth > 3 then return end
                    local function each(child)
                        if try(child, "hidden") == true then pcall(function() child.hidden = false end) end
                        show(child, depth + 1)
                    end
                    pcall(function() parent:IterateDynamicComponents(each) end)
                    pcall(function() parent:IterateStaticComponents(each) end)
                end
                show(component, 1)
            end
        end
    end
end

----------------------------------------------------------------
-- HIDDEN BARS AND LAYOUT CHANGES
----------------------------------------------------------------
local watchPass = 0
local collapsed = {}                 -- interface id -> true while its first component has no size (the bar is hidden: seen in game as 0x0)
local secondRescaleAt, reshowReportAt = nil, nil
local WINDOW_STABLE_PASSES = 5      -- a window counts as "where the player put it" once it has stayed put for this many looks
local windowStable, windowPending, frozenWindows = {}, {}, nil      -- the places of the windows over the last few looks while no bar was hidden; the oldest is kept when one is hidden
local reshowAt = nil                 -- watch pass at which a bar that was hidden got its size back
local holdSaveUntil = -1             -- places are not saved until this watch pass (the game moves things while a bar is hidden or coming back)

-- the action bar settings and number buttons sit in ACTIONBAR_SCROLLER at the bar's right end. Seen in game: when a hidden bar comes back the
-- game puts the scroller somewhere else (x 545, where it had been 608), so the place it had while all bars were shown is kept and put back
function X.eachScroller(action)
    for bar = 1, 8 do
        local prefix = "TOPLEVEL_V2_COMBAT_BAR" .. (bar > 1 and tostring(bar) or "") .. "__"
        local ok, value = pcall(function() return id.Component[prefix .. "ACTIONBAR_SCROLLER"] end)
        value = ok and tonumber(tostring(value)) or nil
        if value and value >= 0 then
            local interfaceID = value // 65536
            local component
            if isLoaded(interfaceID) then pcall(function() component = ui.Interfaces:GetComponent(interfaceID, value % 65536) end) end
            if component then action(bar, interfaceID, component) end
        end
    end
end

-- Where the scroller sits is worked out, not remembered: in the normal (modern) layout it is at 507 before scaling in every bar (608 at 120%, in
-- all five bars). What was remembered went wrong twice: it was taken from a bar that was hidden (x 251), and in classic mode the game puts the
-- scroller further right (630 at 120%), which was kept when the layout changed back, leaving a wider gap. The classic layout is the one with
-- the wider interface (548 before scaling, against 526), and is left alone.
local SCROLLER_X = 507
local MODERN_WIDTH_LIMIT = 540       -- a frame narrower than this (the game's own width: 530 and 526 in modern, 552 and 548 in classic) is the modern layout

-- Classic mode has no shapes: all the bars, the main one too, are 1x14 there. The mode is read from the width of the frame the main bar sits in (as in
-- X.stateText), and has to read the same a few times in a row before it is believed (the window flips between its own size and the scaled one while it
-- is dragged).
function X.classicWatch()
    local frame
    pcall(function() frame = ui.Interfaces:GetComponent(1477, 72) end)
    local w = frame and try(frame, "width")
    if type(w) ~= "number" or percent <= 0 then return end
    -- The window 1477:69 around the main bar is 4 taller than the frame 1477:72 inside it (127 round a 123 frame at 120%, 2 rows). Now and then
    -- it was left far taller (145) with a gap under the abilities: its height was not one of the sizes that are held, so nothing put it right.
    -- Only a clear difference is touched (the scaled frame sizes differ by a pixel from this rule in the ordinary case).
    X.windowTick = (X.windowTick or 0) + 1
    if X.windowTick % 8 == 0 and not (X.holdPaused or X.layoutChangedAt or X.rebuilding or X.resizing or X.startRescaleAt) and not X.isHiddenBar(1430) then
        pcall(function()
            local window = ui.Interfaces:GetComponent(1477, 69)
            local inner = try(frame, "height")
            local outer = window and try(window, "height")
            if type(inner) == "number" and type(outer) == "number" and inner > 0 and math.abs(outer - (inner + 4)) > 3 then
                X.windowFixAt = (X.windowFixAt or 0)
                if X.windowFixAt < 8 then
                    X.windowFixAt = X.windowFixAt + 1
                end
                -- (the hold keeps writing the target it has for this window, which was worked out from a size the game had only for a moment:
                -- a height put here alone was put back to the wrong one on the next frame)
                X.setWindowTarget(69, inner + 4)
                setProperty(window, "height", inner + 4)
            end
        end)
    end
    local reading = (w * 100 / percent) >= MODERN_WIDTH_LIMIT
    -- (while the bars are put back to the game's own sizes for a new layout to be read, the frame is not scaled, and dividing its width by the percent
    -- made classic (548) read as modern until the bars were scaled again: the mode was only noticed after the whole re-read was done, and then
    -- the whole re-read was done a second time, which was most of the delay going modern -> classic)
    if X.holdPaused or X.layoutChangedAt then reading = w >= MODERN_WIDTH_LIMIT end
    if reading == X.classicReading then
        X.classicSame = (X.classicSame or 0) + 1
    else
        X.classicReading, X.classicSame = reading, 1
    end
    if X.classicSame >= 6 and X.classicMode ~= reading then
        local first = X.classicMode == nil
        X.classicMode = reading
        -- (a switch between modes from a shape other than 1x14 changes the frames by far more than the jump the layout check looks for, so it was
        -- never noticed and the old shapes were held over the other mode's layout: the same pause and re-read is started here)
        -- (loading straight into classic with the lock hidden: the bars were laid out before the mode was known, with the modern strip for the lock
        -- (21) and not classic's (30), so they did not reach over it: the layout is taken again now that it is known)
        local lockRedo = first and reading and lockHidden
        if (not first or lockRedo) and next(sets) ~= nil and not (X.holdPaused or X.layoutChangedAt or X.rebuilding or X.resizing) then
            X.holdPaused, X.pausedAt, X.layoutChangedAt = true, X.watchPass or 0, X.watchPass or 0
            pcall(X.unscaleUntouched)
        end
        if reading then
            -- (the shapes the bars had are kept to give them back when classic ends; the game keeps its own settings but they are read over by
            -- the 1x14 layouts laid out here)
            if not X.preClassic then
                X.preClassic = { main = X.shapeIndex or 1, extras = {}, done = {}, started = first }
                for id, state in pairs(X.extraShape or {}) do
                    if type(state.applied) == "number" and state.applied >= 1 then X.preClassic.extras[id] = state.applied end
                end
            end
            X.shapeIndex = 1
            if Engine.shapeCallback then pcall(Engine.shapeCallback, 1) end
        else
            -- (back in modern: the shape the main bar's frame has now; the extra bars follow their windows)
            -- (the shapes the game has just given the windows are taken now, before the plugin scales or holds them again: later they have been
            -- seen at the classic size and scaled, which read as 1x14)
            do
                local seen = { extras = {} }
                seen.main = X.mainShapeFromWindow()
                for _, entry in ipairs(X.EXTRA_SHAPE_BARS) do
                    local c
                    pcall(function() c = ui.Interfaces:GetComponent(1477, entry[2]) end)
                    seen.extras[entry[1]] = c and X.extraShapeOf(try(c, "width"), try(c, "height")) or nil
                end
                X.leaveSeen = seen
                local parts = {}
                for id, shape in pairs(seen.extras) do parts[#parts + 1] = id .. "=" .. shape end
            end
            local back = X.preClassic and X.preClassic.main or X.shapeNow()
            if back then X.shapeIndex = back end
            if Engine.shapeCallback then pcall(Engine.shapeCallback, X.shapeIndex or 1) end
        end
    end
    -- (while it lasts the main bar stays 1x14 whatever the game's frame looks like)
    if X.classicMode and X.shapeIndex ~= 1 then X.shapeIndex = 1 end
end
function X.restoreScrollers(why)
    if percent <= 0 then return end
    X.eachScroller(function(bar, interfaceID, component)
        if interfaceID == 1430 and X.shapeIndex and X.shapeIndex ~= 1 then return end      -- (the shape sets its own place)
        -- (an extra bar in a shape other than 1x14 has its scroller placed by the shape: the settings and number buttons sit in it, and putting it at the
        -- 1x14 bar's place (608 at 120%) took them off the end of a 2x7 bar when the bars came back from classic mode)
        if interfaceID ~= 1430 and not X.classicMode then
            for _, entry in ipairs(X.EXTRA_SHAPE_BARS) do
                if entry[1] == interfaceID then
                    local window
                    pcall(function() window = ui.Interfaces:GetComponent(1477, entry[2]) end)
                    local shape = window and X.extraShapeOf(try(window, "width"), try(window, "height"))
                    if shape and shape ~= 1 then return end
                end
            end
        end
        -- (only an interface that has been scaled. Which layout it has is read from the width the GAME gave the frame the bars sit in: the
        -- plugin holds the bars at the size it set, so their own width does not show what the game has done after a switch between modes)
        local set = sets[interfaceID]
        if not (set and set.held) then return end
        local gameWidth
        for _, item in ipairs(set.held) do
            if item.frameKey and not item.adaptive then
                local base = item.trueBase or item.base
                local w = X.gameFrameWidth[item.frameKey] or (type(base) == "table" and base.width or nil)
                if type(w) == "number" and w > 300 and w < 1000 then gameWidth = w; break end
            end
        end
        if not gameWidth then return end
        local classic = gameWidth >= MODERN_WIDTH_LIMIT
        -- (the layout is the same for all the bars. Bars 4 and 5 are hidden in classic, so the widths held for their frames are not the game's
        -- and read as classic (632) when the game was in modern, which put the scroller of bar 5 at 731, off the bar. They follow bars 1 to 3.)
        if bar >= 4 then
            -- (the mode the plugin has read from the main bar's frame. The main bar's own entry is not updated while it has a shape other than
            -- 1x14, and was left at classic: the scroller of bars 4 and 5 was put at the classic place, off the bar, with the cog and page number)
            local reference = X.classicMode
            if reference == nil then reference = X.layoutSaid[1430] end
            if reference == nil then reference = X.layoutSaid[1670] end
            if reference ~= nil then classic = reference end
        end
        if X.layoutSaid[interfaceID] ~= classic then
            X.layoutSaid[interfaceID] = classic
        end
        -- (the classic layout has its own place for the scroller: the game puts it 23 in from the frame's right edge there, 19 in modern.
        -- 525 in a 548 frame, and 609 in the 632 frame of bars 4 and 5, which matches the 730 at 120% seen there)
        local rawX = SCROLLER_X
        if classic then rawX = bar >= 4 and 609 or math.floor(gameWidth - 23 + 0.5) end
        local wanted = math.floor(rawX * percent / 100 + 0.5)
        local x = try(component, "x")
        if x ~= wanted then
            pcall(function() component:SetX(wanted) end)
            if X.restoredScrollerLines < 30 then
                X.restoredScrollerLines = X.restoredScrollerLines + 1
            end
        end
        -- the place the plugin keeps for it is the right one too (a rescale makes it again from where the game has it, and turning the plugin
        -- off puts the pieces back to their size-100 place)
        do
            for _, item in ipairs(set.held) do
                if item.component == component then
                    if item.target then item.target.x = wanted end
                    for _, base in ipairs({ item.base or false, item.trueBase or false }) do
                        if type(base) == "table" then base.x = rawX end
                    end
                end
            end
            for _, list in ipairs({ set.originals or false, set.trueBase or false }) do
                local base = type(list) == "table" and list[component]
                if type(base) == "table" then base.x = rawX end
            end
        end
        -- the main bar's buttons (COMBATBAR_BUTTONS) sit at the same x as its scroller (525 and 525 in classic). While the modern layout is
        -- being made the game puts both too far right (573), which the plugin scaled to 688: past the right edge of the bar (605 wide), so
        -- they were not seen. They follow the scroller's place. (A guess for modern: it is the classic relation, not one seen in modern.)
        if bar == 1 then
            local number = staticOf("COMBATBAR_BUTTONS", 1430)
            local buttons
            if number then pcall(function() buttons = ui.Interfaces:GetComponent(1430, number) end) end
            if buttons then
                if try(buttons, "x") ~= wanted then pcall(function() buttons:SetX(wanted) end) end
                local wantKey = "1430:" .. number
                for _, item in ipairs(set.held) do
                    if not item.key and item.component and keyOf(item.component) == wantKey then
                        if item.target then item.target.x = wanted end
                        for _, base in ipairs({ item.base or false, item.trueBase or false }) do
                            if type(base) == "table" then base.x = rawX end
                        end
                    end
                end
                for _, list in ipairs({ set.originals or false, set.trueBase or false }) do
                    if type(list) == "table" then
                        for other, base in pairs(list) do
                            if type(base) == "table" and keyOf(other) == wantKey then base.x = rawX end
                        end
                    end
                end
            end
        end
    end)
end

-- Classic combat mode puts the bars at the bottom of the screen and they cannot be moved there. When the plugin starts in it, the saved places
-- (where the bars were in the normal mode) must not be put back: the other bars show as a first component of 0x0 then.
-- a hidden bar (classic mode, or hidden by the player) shows as a first component of 0x0
function X.isHiddenBar(interfaceID)
    local anchor
    pcall(function() anchor = ui.Interfaces:GetComponent(interfaceID, 0) end)
    local w, h = anchor and try(anchor, "width"), anchor and try(anchor, "height")
    return type(w) == "number" and type(h) == "number" and (w == 0 or h == 0)
end

function X.anyBarHidden()
    for _, id in ipairs(INTERFACES) do
        if id ~= 1430 and isLoaded(id) then
            local anchor
            pcall(function() anchor = ui.Interfaces:GetComponent(id, 0) end)
            local w, h = anchor and try(anchor, "width"), anchor and try(anchor, "height")
            if type(w) == "number" and type(h) == "number" and (w == 0 or h == 0) then return true end
        end
    end
    return false
end

-- A number that changes when any size or place the plugin holds is different in the game: used to see when the game has finished laying
-- the bars out after a change of combat mode (it can lag for a moment, and sizes taken from it half way are wrong).
function X.layoutSignature()
    local sum, mix = 0, 1
    for _, set in pairs(sets) do
        for _, item in ipairs(set.held) do
            local c = item.component
            if c and not item.adaptive then
                local w, h, x, y = try(c, "width"), try(c, "height"), try(c, "x"), try(c, "y")
                if type(w) == "number" and type(h) == "number" and type(x) == "number" and type(y) == "number" then
                    mix = (mix % 9973) + 1
                    sum = (sum + mix * (w * 31 + h * 17 + x * 7 + y * 3)) % 1000000007
                end
            end
        end
    end
    return sum
end

-- THE CLASSIC STACK. In the classic layout the three bars sit one above the other, bottom-aligned, with no gaps, and cannot be dragged. The
-- game spaces their windows by their normal heights, so when the bars are scaled they overlap (bigger) or leave gaps (smaller) until the game
-- lays the stack out again, which it does when an interface is opened or closed. Seen in game: after that the lowest window sits on the bottom
-- edge of the screen and each window above it ends exactly where the one below begins. So the same is done here whenever the sizes change.
X.STACK = { { 69, 1430 }, { 74, 1670 }, { 79, 1671 }, { 84, 1672 }, { 89, 1673 } }    -- window number, and the interface it holds
local STACK_BOTTOM_REACH = 60      -- the lowest window counts as sitting on the screen's bottom edge when it is within this many pixels of it

function X.restackClassic()
    if X.layoutSaid[1430] ~= true or X.holdPaused or X.layoutChangedAt then return end
    local list = {}
    for _, entry in ipairs(X.STACK) do
        if isLoaded(entry[2]) and not X.isHiddenBar(entry[2]) then
            local component
            pcall(function() component = ui.Interfaces:GetComponent(1477, entry[1]) end)
            local x, y, h = component and try(component, "x"), component and try(component, "y"), component and try(component, "height")
            if type(x) == "number" and type(y) == "number" and type(h) == "number" and h > 0 then
                list[#list + 1] = { component = component, x = x, y = y, h = h }
            end
        end
    end
    if #list < 2 then return end
    table.sort(list, function(a, b) return a.y < b.y end)
    for i = 2, #list do
        if math.abs(list[i].x - list[1].x) > 1 then return end       -- not one column: not the classic stack
    end
    local function place(item, y)
        if item.y ~= y then
            pcall(function() item.component:SetY(y) end)
            item.y = y
        end
    end
    -- the lowest window sits on the bottom edge of the screen (the container all the windows are in)
    local screen
    pcall(function() screen = try(ui.Interfaces:GetComponent(1477, 61), "height") end)
    local lowest = list[#list]
    if type(screen) == "number" and math.abs(lowest.y + lowest.h - screen) <= STACK_BOTTOM_REACH then place(lowest, screen - lowest.h) end
    for i = #list - 1, 1, -1 do place(list[i], list[i + 1].y - list[i].h) end
end

----------------------------------------------------------------
-- STATE TRACKER
-- The state the bars are in: combat mode (modern or classic), locked or not, background hidden or not, which bars are hidden, and the
-- percent. Each change is printed at once.
----------------------------------------------------------------
-- THE LOCK STATE. TOPLEVEL_V2_CUSTOMIZATION_LOCK is 1 when the interface is locked (it is bit 2 of TOPLEVEL_V2_SKINS_VARP, which is 9 unlocked,
-- 11 locked, and 26 in classic mode where the bars cannot be unlocked). It is read each pass; the change of TOPLEVEL_V2_SKINS_VARP is also
-- listened for, which comes a moment earlier, and gives the same answer from its value. Engine.onLockChange(locked) is called on a change.
Engine.onLockChange = nil
X.lockedNow = nil          -- nil until it has been read

local function readVarValue(name)
    for _, kind in ipairs({ "VarPlayer", "Player", "VarClient" }) do
        local ok, value = pcall(function() return var[kind][name].value end)
        value = ok and tonumber(value) or nil
        if value then return value end
    end
    return nil
end

function X.setLocked(locked, why)
    if locked == X.lockedNow then return end
    local wasKnown = X.lockedNow ~= nil
    X.lockedNow = locked
    if (X.lockLines or 0) < 100 then
        X.lockLines = (X.lockLines or 0) + 1
    end
    -- (an upright bar: the game lays it out again when the interface is locked or unlocked, so its fills are looked at again as after a drag)
    if X.shapeIndex and X.shapeIndex >= 3 and sets[1430] then
        -- (the same watching as the flat bar gets, but for as long as the game takes to lay the upright bar out: every piece is looked at before
        -- each frame is drawn, and pieces the game made again are scaled at once, so nothing is drawn at the game's sizes)
        forceFrames = math.max(forceFrames, 120)
        -- (the game made the status bar pieces again, with their own sizes: the fills came back four high and at the game's places, as the log
        -- showed. The bar is laid out again from the start, after the game has finished, and once more later in case it was not done yet.)
        -- (no full layout afterwards: laying everything out again showed as a flicker. The pieces are put right where they stand, before each frame.)
    end
    if Engine.onLockChange then pcall(Engine.onLockChange, locked) end
end

-- The padlock on the action bar is a different lock: it keeps the ability slots from being dragged. COMBATV2_GENERIC_BASE_VAR_1, bit 4:
-- 150994960 locked, 150994944 unlocked. Engine.onBarsLockChange(locked) is called on a change (the padlock icon follows it).
Engine.onBarsLockChange = nil
X.barsLocked = nil

function X.setBarsLocked(locked, why)
    if locked == X.barsLocked then return end
    X.barsLocked = locked
    if (X.barsLockLines or 0) < 100 then
        X.barsLockLines = (X.barsLockLines or 0) + 1
    end
    if Engine.onBarsLockChange then pcall(Engine.onBarsLockChange, locked) end
end

function X.pollLock()
    local slots = readVarValue("COMBATV2_GENERIC_BASE_VAR_1")
    if slots ~= nil and slots ~= X.polledSlots then
        X.polledSlots = slots
        X.setBarsLocked(math.floor(slots / 16) % 2 == 1, "COMBATV2_GENERIC_BASE_VAR_1 is " .. tostring(slots))
    end
    local bit = readVarValue("TOPLEVEL_V2_CUSTOMIZATION_LOCK")
    if bit ~= nil then
        -- (only when it changes, so a read that comes late after the change event does not undo it)
        if bit ~= X.polledBit then
            X.polledBit = bit
            X.setLocked(bit == 1, "TOPLEVEL_V2_CUSTOMIZATION_LOCK is " .. tostring(bit))
        end
    elseif X.lockedNow == nil then
        -- (the varbit could not be read: its bit of TOPLEVEL_V2_SKINS_VARP gives the same)
        local skins = readVarValue("TOPLEVEL_V2_SKINS_VARP")
        if skins then X.setLocked(math.floor(skins / 2) % 2 == 1, "TOPLEVEL_V2_SKINS_VARP is " .. tostring(skins)) end
    end
end

function X.stateText()
    local classic = "mode unknown"
    local frame
    pcall(function() frame = ui.Interfaces:GetComponent(1477, 72) end)
    local w = frame and try(frame, "width")
    if type(w) == "number" and percent > 0 then
        -- (the width the game has for it before scaling: 526 or 530 in modern, 548 or 552 in classic)
        classic = (w * 100 / percent) >= MODERN_WIDTH_LIMIT and "classic" or "modern"
    end
    local hiddenBars = {}
    for _, interfaceID in ipairs(INTERFACES) do
        if collapsed[interfaceID] then hiddenBars[#hiddenBars + 1] = tostring(interfaceID) end
    end
    -- (the read only gives the value at the start: once the variable has changed, what the change event said is used, since the value read
    -- stayed at 150994960 whether the interface was locked or not)

    local lock = (X.lockedNow == nil and "interface lock unknown" or (X.lockedNow and "interface locked" or "interface unlocked"))
        .. ", " .. (X.barsLocked == nil and "slot lock unknown" or (X.barsLocked and "slots locked" or "slots unlocked"))
    local hide = (hideParts.BACKGROUND and hideParts.BORDER) and "background hidden" or "background shown"
    return table.concat({ classic, lock, hide, "hidden bars: " .. (#hiddenBars > 0 and table.concat(hiddenBars, " ") or "none"), "percent " .. tostring(percent) }, ", ")
end

function X.watchState()
    pcall(X.pollLock)
    local text = X.stateText()
    if text ~= X.stateText_ then
        X.stateText_ = text
    end
end

function Engine.tick()
    watchTicks = watchTicks + 1
    if watchTicks < WATCH_EVERY then return end
    watchTicks = 0
    watchPass = watchPass + 1
    X.watchPass = watchPass
    pcall(X.watchState)
    if X.classicStart and not X.anyBarHidden() then
        X.classicStart = false
    end
    -- (the scrollers are looked at on every pass while things are happening and every third pass otherwise)
    if watchPass % 3 == 0 or frame - (X.lastBusy or 0) <= QUIET_AFTER then pcall(X.restoreScrollers, "kept") end
    pcall(X.restackClassic)
    pcall(watchWindows)
    for _, id in ipairs(INTERFACES) do
        local set = sets[id]
        local loadedNow = isLoaded(id)
        if loadedNow then
            -- a hidden bar shows as a first component of 0x0; when it has a size again the game has made its pieces again at their own size
            local anchor
            pcall(function() anchor = ui.Interfaces:GetComponent(id, 0) end)
            local w, h = anchor and try(anchor, "width"), anchor and try(anchor, "height")
            local collapsedNow = type(w) == "number" and type(h) == "number" and (w == 0 or h == 0)
            local wasCollapsed = collapsed[id]
            if wasCollapsed and not collapsedNow then  end
            if collapsedNow and not wasCollapsed then  end
            if wasCollapsed and not collapsedNow then reshowAt = reshowAt or watchPass end
            collapsed[id] = collapsedNow or nil
            if collapsedNow then X.wasHidden[id] = true end
            if collapsedNow then
                holdSaveUntil = watchPass + 4
                if not frozenWindows then
                    -- (the places the windows had been steady at: what the game does to them as it hides the other bars is not kept)
                    frozenWindows = {}
                    for key, place in pairs(windowStable) do frozenWindows[key] = place end
                    windowPending = {}
                    for _, other in pairs(sets) do other.posPending = {} end
                end
            end
        else
            collapsed[id] = nil
        end
        if not loadedNow then
            loadedStreak[id] = 0
            if set then forgetSet(id) end
        else
            loadedStreak[id] = (loadedStreak[id] or 0) + 1
            if set and set.anchor and type(try(set.anchor, "staticID")) ~= "number" and type(try(set.anchor, "width")) ~= "number" then
                forgetSet(id)         -- the interface was built again; its components are new
                set = nil
            end
            -- (not while the bar is hidden: scaled then, its 0x0 would be held and the bar would stay empty when it is shown)
            if not set and (percent > 100 or everScaled) and loadedStreak[id] >= SETTLE_CHECKS and not collapsed[id] then
                local scaled = scaleInterface(id, percent)
                if scaled and sets[id] then
                    -- scaled at start (or after a relog): the saved place is put back
                    if percent > 100 and not X.classicStart then restorePositions(sets[id]) else sets[id].posReady = true end
                end
            elseif set and percent > 100 and settleLeft == 0 and (screenKey == nil or screenKey == baseKey) and watchPass > holdSaveUntil and not reshowAt and not X.classicStart then
                savePositions(set)
            end
        end
    end
    -- a bar that was hidden is back (for a couple of passes now): everything is scaled again from what the game has now, and the places
    -- are put back where they were before it was hidden
    if next(collapsed) == nil and not reshowAt and not secondRescaleAt then
        frozenWindows = nil
        local snapshot = {}
        pcall(snapshotWindows, snapshot)
        for key, place in pairs(snapshot) do
            local pending = windowPending[key]
            if pending and pending.x == place.x and pending.y == place.y then
                pending.count = pending.count + 1
            else
                pending = { x = place.x, y = place.y, count = 1 }
                windowPending[key] = pending
            end
            if pending.count >= WINDOW_STABLE_PASSES then windowStable[key] = { x = place.x, y = place.y } end
        end
    end
    -- (once a pass after it is shown, and again a few passes later in case the game was still laying it out)
    -- the action bar settings and number buttons (under ACTIONBAR_SCROLLER): not known why they stay hidden after the bar comes back,
    -- so what they are before and after is printed
    local function rescaleAfterShown(why)
        pcall(function()
            Engine.setPercent(percent)
            showSettingsLayers()
            X.restoreScrollers(why)
            if percent > 100 then
                for _, set in pairs(sets) do restorePositions(set) end
            end
            applyWindows(frozenWindows, true)
        end)
        reshowReportAt = watchPass + 1
    end
    -- (not while a new layout is still being taken from the game: that is scaled first, and these follow it)
    if reshowAt and not X.layoutChangedAt then
        secondRescaleAt = watchPass + 4
        reshowAt = nil
        holdSaveUntil = watchPass + 6
        rescaleAfterShown("first")
    elseif secondRescaleAt and watchPass >= secondRescaleAt and not X.layoutChangedAt then
        secondRescaleAt = nil
        rescaleAfterShown("second")
        frozenWindows = nil
    end
    -- the other combat mode's layout came in (classic <-> modern), or the client started in classic: scaled again from what the game has now
    -- (the holding is never paused for long, whatever else is going on)
    if X.holdPaused and watchPass >= (X.pausedAt or 0) + 15 then X.holdPaused = false end
    local layoutDue = X.layoutChangedAt and watchPass >= X.layoutChangedAt + 2
    -- (the new layout is only taken from the game once its sizes have stopped changing: a game that lags while it changes mode is still
    -- laying the bars out, and the sizes it has half way would be scaled from for good)
    if layoutDue and X.holdPaused and watchPass < X.layoutChangedAt + LAYOUT_WAIT_MAX then
        local signature = X.layoutSignature()
        if signature ~= X.layoutSig then
            X.layoutSig, X.layoutSame = signature, 0
        else
            X.layoutSame = (X.layoutSame or 0) + 1
        end
        if X.layoutSame < LAYOUT_STABLE_PASSES then
            layoutDue = false
            if not X.layoutWaitSaid then
                X.layoutWaitSaid = true
            end
        end
    end
    -- (not while a new layout is being taken: that scaling does this too, and one made over the game's half-laid-out sizes lost them)
    local startDue = X.startRescaleAt and watchPass >= X.startRescaleAt and not X.holdPaused and not X.layoutChangedAt
    -- (hidden bars do not hold this up: the other layout comes in whether or not a bar is hidden, and hidden bars are left alone)
    if layoutDue or (startDue and next(collapsed) == nil and not reshowAt and not secondRescaleAt) then
        X.layoutChangedAt, X.startRescaleAt = nil, nil
        X.layoutSig, X.layoutSame, X.layoutWaitSaid = nil, 0, false
        X.layoutRescale = layoutDue and true or false
        if layoutDue and X.holdPaused then pcall(X.absorbLayout) end
        X.holdPaused = false
        pcall(Engine.setPercent, percent)
        X.layoutRescale = false
        -- (a safety net: the game can lag while it changes mode and still be building the bars when the scaling above runs, which has left
        -- the button backgrounds wrong now and then. Everything is scaled once more a little later, when it has settled.)
        X.recheckAt = watchPass + RECHECK_AFTER
    elseif startDue and next(collapsed) ~= nil then
        X.startRescaleAt = nil
    end
    if X.recheckAt and watchPass >= X.recheckAt and not X.holdPaused and not X.layoutChangedAt and not X.startRescaleAt and not reshowAt and not secondRescaleAt then
        X.recheckAt = nil
        pcall(Engine.setPercent, percent)
    end
    if reshowReportAt and watchPass >= reshowReportAt then
        reshowReportAt = nil
        pcall(X.restoreScrollers, "a pass later")
    end
end

----------------------------------------------------------------
-- START AND SHUTDOWN
----------------------------------------------------------------
-- called once when the plugin starts: interfaces that are already on screen are scaled straight away (no waiting to see them settle)
-- Summoning bar mode: false = summoning points, true = the familiar's special attack points (NOTES_VARP2, bit 8 clear)
X.summonSpecial = false
function Engine.getSummonSpecial() return X.summonSpecial == true end
function X.setSummonSpecial(on, why)
    if on == X.summonSpecial then return end
    X.summonSpecial = on
end

-- (for the meter: each of the things the draw handler calls is counted on its own, so the one that costs the frames can be named; with the
-- meter off Perf.wrap hands the function back untouched)
-- THE MINIMISE BUTTON ON THE UPRIGHT SHAPES: the game shrinks the frame (1477:72) to the width of the status bars alone, but the player info (1430:6)
-- is held at its place beside the abilities (x 85 in a 7x2 bar), which is outside the shrunk frame: the status bars were not seen. While the frame
-- is much narrower than it has been in this shape the info is put at x 0 (and held there), and its place is given back when the frame is wide again.
function X.collapseInfo()
    local shape = X.shapeIndex or 1
    -- (not while the frames are at the game's own size for a drag: they are narrower than the scaled ones, which read as the bar being minimised, and
    -- the status bars and the abilities flicked between the two states with every drag)
    if (DragFix.flipped and DragFix.flipped()) or (DragFix.boxVisible and DragFix.boxVisible()) or X.resizing or X.rebuilding or X.holdPaused then return end
    local function layerOf()
        local n = staticOf("ACTIONBAR_LAYER", 1430)
        local c
        if n then pcall(function() c = ui.Interfaces:GetComponent(1430, n) end) end
        return c
    end
    if X.classicMode or shape == 1 or shape == 2 or percent <= 0 then
        X.minimised = nil
        -- (the shape changed while the layer was hidden: it is shown again, or the abilities stayed invisible when the shape came back)
        if X.layerHidden then
            local c = layerOf()
            if c then pcall(function() c.hidden = false end) end
            X.layerHidden = nil
        end
        return
    end
    local set = sets[1430]
    local number = staticOf(PLAYER_INFO, 1430)
    if not set or not set.held or not number then return end
    local frame
    pcall(function() frame = ui.Interfaces:GetComponent(1477, 72) end)
    local width = frame and try(frame, "width")
    if type(width) ~= "number" or width <= 0 then return end
    -- (found once for a list of held pieces, as this runs on every frame)
    local found = X.infoItem
    if not (found and X.infoItemFor == set.held and X.infoItemN == #set.held) then
        found = nil
        for _, candidate in ipairs(set.held) do
            if candidate.component and not candidate.adaptive and keyOf(candidate.component) == "1430:" .. number then found = candidate; break end
        end
        X.infoItem, X.infoItemFor, X.infoItemN = found, set.held, #set.held
    end
    for _, item in ipairs(found and { found } or {}) do
        if item.target and type(item.target.x) == "number" and type(item.target.width) == "number" then
            -- (collapsed: the frame is too narrow to hold the abilities and then the info, which is at its own place beside them. This is worked
            -- from the sizes of the shape that is on now, so a bar that is collapsed when its shape is changed is known to be collapsed at once)
            -- (a layout made again while collapsed wrote the info's own place back: that is the place to remember now)
            if item.collapsedFrom ~= nil and item.target.x ~= 0 then
                -- (only a new shape gives the info a new place of its own: anything else written to it while it is collapsed is put straight back to 0,
                -- or the place remembered moved a little with every collapse and the status bars crept across the screen)
                if item.collapsedShape ~= shape then
                    item.collapsedFrom, item.collapsedShape = item.target.x, shape
                end
                item.target.x = 0
                setProperty(item.component, "x", 0)
                if type(item.seen) == "table" then item.seen.x = try(item.component, "x") end
            end
            -- (while the bar is open its place is remembered on every look, so that the one that is given back is the last good one)
            if item.collapsedFrom == nil and width >= 0.8 * (item.target.x + item.target.width) then item.openX, item.openShape = item.target.x, shape end
            local infoX = item.collapsedFrom or item.target.x
            local collapsed = width < 0.8 * (infoX + item.target.width)
            X.minimised = collapsed      -- (read by the drag fix, which needs to know which size the game has the frames at)
            local layer = layerOf()
            if layer then
                if collapsed then
                    if try(layer, "hidden") ~= true then pcall(function() layer.hidden = true end); X.layerHidden = true end
                elseif X.layerHidden then
                    pcall(function() layer.hidden = false end)
                    X.layerHidden = nil
                end
            end
            if collapsed and item.collapsedFrom == nil then
                item.collapsedFrom = (item.openShape == shape and item.openX) or item.target.x
                item.collapsedShape = shape
                item.target.x = 0
                if item.home and item.home.x then item.homeX = item.home.x; item.home.x = 0 end
                setProperty(item.component, "x", 0)
                if type(item.seen) == "table" then item.seen.x = try(item.component, "x") end
            elseif not collapsed and item.collapsedFrom ~= nil then
                item.target.x = item.collapsedFrom
                if item.home and item.homeX then item.home.x = item.homeX end
                setProperty(item.component, "x", item.collapsedFrom)
                if type(item.seen) == "table" then item.seen.x = try(item.component, "x") end
                item.collapsedFrom, item.homeX = nil, nil
            end
            return
        end
    end
end

function X.wrapDrawParts()
    for _, name in ipairs({ "drawTick", "slotBgTick", "centreStatusText", "classicWatch", "extraShapeStep", "extraEarly", "refreshVars", "castHit",
        "holdAll", "repairTurned", "driveStatusFills", "shapeProbe", "applyOther", "applyLock", "applyExpand" }) do
        if type(X[name]) == "function" then X[name] = Perf.wrap("draw part: " .. name, X[name]) end
    end
end
X.wrapDrawParts()

function Engine.start()
    DragFix.attach({
        sets = function() return sets end,
        try = try,
        keyOf = keyOf,
        tolerance = READBACK_TOLERANCE,
        -- (the size the game knows a frame of the main bar by: the minimised one while the bar is minimised, for the frames that change with it)
        native = function(number, base)
            if number ~= 72 and number ~= 73 and number ~= 69 then return nil end
            -- (worked out once for all the frames of a release: the first frame put to its native size would change what the next one reads)
            local stamp = tostring(X.drawCount) .. ":" .. tostring(X.logicCount)
            if X.nativeStamp ~= stamp then
                X.nativeStamp, X.nativeIndex = stamp, nil
                -- (the upright shapes know whether they are minimised from their own check, which also holds for two columns of status bars: the
                -- frame is wider than the game's then, and its size did not match the minimised one)
                if X.minimised and (X.shapeIndex == 3 or X.shapeIndex == 4) then X.nativeIndex = X.shapeIndex; return X.COLLAPSED_SHAPES[X.shapeIndex][1] + (number == 72 and 0 or 4), X.COLLAPSED_SHAPES[X.shapeIndex][2] + (number == 72 and 0 or 4) end
                local frame
                pcall(function() frame = ui.Interfaces:GetComponent(1477, 72) end)
                local w, h = frame and try(frame, "width"), frame and try(frame, "height")
                if type(w) == "number" and type(h) == "number" and percent > 0 then
                    local index, minimised = X.shapeIndexOf(math.floor(w * 100 / percent + 0.5), math.floor(h * 100 / percent + 0.5))
                    if index and minimised then X.nativeIndex = index end
                end
            end
            local index = X.nativeIndex
            if not index then return nil end
            local extra = number == 72 and 0 or 4
            return X.COLLAPSED_SHAPES[index][1] + extra, X.COLLAPSED_SHAPES[index][2] + extra
        end,
        -- (the frames must not be touched while the bars are being laid out again)
        busy = function() return X.holdPaused or X.layoutChangedAt or X.startRescaleAt or X.classicStart or X.resizing end,
    })
    DragFix.start()
    -- (the extra bars' shape handling must also run at 100%, where nothing is held and the engine's own draw event is not subscribed)
    pcall(function()
        Event.Draw.Subscribe("BetterActionBars_extras", function()
            if holding then return end
            X.drawCount = (X.drawCount or 0) + 1
            if X.drawCount % 3 == 0 then pcall(X.classicWatch); pcall(X.extraShapeStep) end
        end)
    end)
    for _, id in ipairs(INTERFACES) do
        if isLoaded(id) then loadedStreak[id] = SETTLE_CHECKS end
    end
    X.holdPaused, X.layoutChangedAt, X.recheckAt = false, nil, nil
    X.classicStart = X.anyBarHidden()
    X.startRescaleAt = X.classicStart and 15 or nil      -- (the game lays the bars out again a little after the client starts in classic mode)
    if X.classicStart then  end
    watchTicks = WATCH_EVERY
    -- (the lock state, whether or not the sizes are being held: held only at above 100%, so onVar is not always listening)
    pcall(function()
        Event.VarTransmit.Subscribe("BAB_STATE_VAR", function(event)
            Perf.tally("var events (state listener)")
            pcall(function() X.noteVar(X.varText(event.var), event.newValue) end)
            if event.oldValue == event.newValue then return end
            local text = X.varText(event.var)
            if string.find(text, "TOPLEVEL_V2_SKINS_VARP", 1, true) then
                local value = tonumber(event.newValue)
                if value then X.setLocked(math.floor(value / 2) % 2 == 1, "TOPLEVEL_V2_SKINS_VARP " .. tostring(event.oldValue) .. " -> " .. tostring(value)) end
            end
            -- the summoning bar shows summoning points or the familiar's special attack points; a click on it changes NOTES_VARP2 (bit 8 clear = special)
            if string.find(text, "NOTES_VARP2", 1, true) then
                local value = tonumber(event.newValue)
                if value then X.setSummonSpecial(math.floor(value / 256) % 2 == 0, tostring(event.oldValue) .. " -> " .. tostring(value)) end
            end
            if string.find(text, "TOPLEVEL_V2_CONFIRM_POPUP_ID", 1, true) then
                local nv, ov = tonumber(event.newValue), tonumber(event.oldValue)
                if nv and ov then
                    local why = text .. " " .. tostring(ov) .. " -> " .. tostring(nv)
                    if ov == 0 and nv ~= 0 then pcall(X.layoutPopup, true, false, why)
                    elseif ov ~= 0 and nv == 0 then pcall(X.layoutPopup, false, true, why) end
                end
            end
            if string.find(text, "COMBATV2_GENERIC_BASE_VAR_1", 1, true) then
                local value = tonumber(event.newValue)
                if value then X.setBarsLocked(math.floor(value / 16) % 2 == 1, "COMBATV2_GENERIC_BASE_VAR_1 " .. tostring(event.oldValue) .. " -> " .. tostring(value)) end
            end
        end)
    end)
    -- (the mode the bar is in when the plugin starts)
    local notes = X.readVar and X.readVar("NOTES_VARP2")
    if notes then X.setSummonSpecial(math.floor(notes / 256) % 2 == 0, "read at start: " .. tostring(notes)) end
    Engine.tick()
end

function Engine.shutdown()
    pcall(function() Event.Draw.Unsubscribe("BetterActionBars_extras") end)
    DragFix.stop()
    afterFrameHook = nil
    pcall(function() Event.WindowSizeChanged.Unsubscribe(WINDOW_KEY) end)
    pcall(function() Event.VarTransmit.Unsubscribe("BAB_STATE_VAR") end)
    keptPositions, screenKey, baseKey, settleLeft, pendingRestore = {}, nil, nil, 0, false
    -- Other Settings: everything that was hidden is shown again, and the layouts that were made longer are put back first, so that the sizes the
    -- bars go back to below are the game's own
    do
        local ids = {}
        for id in pairs(otherHidden) do ids[#ids + 1] = id end
        for _, id in ipairs(ids) do
            for static in pairs(otherHidden[id]) do otherHidden[id][static] = false end
            pcall(X.applyOther, id)
        end
        lockHidden, expandHidden = false, false
        pcall(X.applyLock)
        pcall(X.applyExpand)
        X.expandButton = nil
        for _, entry in ipairs(X.EXTRA_SHAPE_BARS) do
            local state = X.extraShape and X.extraShape[entry[1]]
            if state and state.otherDone then
                local shape = (state.applied and state.applied > 0) and state.applied or 1
                pcall(X.rebuildExtra, entry[1], shape)
            end
        end
        X.mainOtherDirty = true
        pcall(X.mainOtherStep)
        X.mainOtherDirty, X.mainOtherLaid = false, false
        otherHidden = {}
        pcall(showSettingsLayers)
    end
    twoRows = false
    if summoningHidden then
        pcall(function() ui.Interfaces:GetComponent(id.Component.TOPLEVEL_V2_COMBAT_BAR__PLAYER_SUMMONING).hidden = false end)
        summoningHidden = false
    end
    if hideBackgrounds then applyHolders(false) end
    hideBackgrounds = false
    if hideFrames then applyFrames(true); pcall(X.placeFrames, false) end
    hideFrames = false
    frameFill = nil
    fillGrow = {}
    fillFit = {}
    hideParts = { BACKGROUND = false, BORDER = false }
    pcall(X.restoreScrollers, "before turning off")      -- (so the size-100 place it goes back to is the right one)
    restoreAll()
    pcall(X.restackClassic)      -- (the bars are back at their own sizes: no gaps left in the classic stack)
    percent = 100
    everScaled = false
    parentBase = {}
    frameHistory = {}
    sets = {}
    updateHolding()
end

-- (the meter in perf.lua counts these as scans; with it off these lines change nothing)
rescanSet = (Perf.section or function(_, fn) return fn end)("  rescanSet", rescanSet)
checkItem = (Perf.section or function(_, fn) return fn end)("  checkItem", checkItem)
drifted = (Perf.section or function(_, fn) return fn end)("  drifted", drifted)
handleHit = (Perf.section or function(_, fn) return fn end)("  handleHit", handleHit)
quickCheck = (Perf.section or function(_, fn) return fn end)("  quickCheck", quickCheck)
X.probeLayout = (Perf.section or function(_, fn) return fn end)("  probeLayout", X.probeLayout)
X.watchState = (Perf.section or function(_, fn) return fn end)("  watchState", X.watchState)
X.restoreScrollers = (Perf.section or function(_, fn) return fn end)("  restoreScrollers", X.restoreScrollers)
X.restackClassic = (Perf.section or function(_, fn) return fn end)("  restackClassic", X.restackClassic)
X.anyBarHidden = (Perf.section or function(_, fn) return fn end)("  anyBarHidden", X.anyBarHidden)
watchWindows = (Perf.section or function(_, fn) return fn end)("  watchWindows", watchWindows)
snapshotWindows = (Perf.section or function(_, fn) return fn end)("  snapshotWindows", snapshotWindows)
isLoaded = (Perf.section or function(_, fn) return fn end)("  isLoaded", isLoaded)
savePositions = (Perf.section or function(_, fn) return fn end)("  savePositions", savePositions)
Engine.holdHidden = (Perf.section or function(_, fn) return fn end)("  holdHidden", Engine.holdHidden)

Engine.statics = Perf.counted(Engine.statics, "scans")
Engine.findSprites = Perf.counted(Engine.findSprites, "scans")
Engine.findSpritesAll = Perf.counted(Engine.findSpritesAll, "scans")

return Engine
