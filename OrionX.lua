local OrionX = {}
OrionX._VERSION = "v1.0.0"
OrionX._BUILD_DATE = "2025-08-17 00:46:00 UTC+07:00"

-- ======== Utilities ========
local Services = setmetatable({}, {__index=function(t,k) local s = game:GetService(k) rawset(t,k,s) return s end})
local HttpService = Services.HttpService
local Players = Services.Players
local RunService = Services.RunService
local UserInputService = Services.UserInputService
local TweenService = Services.TweenService

local function typeofx(v) -- robust typeof fallback
	local ok, tv = pcall(function() return typeof(v) end)
	return ok and tv or type(v)
end

local function deepMerge(dst, src)
	for k,v in pairs(src) do
		if type(v)=="table" and type(dst[k])=="table" then
			deepMerge(dst[k], v)
		else
			dst[k]=v
		end
	end
	return dst
end

local function cloneTable(t)
	local r = {}
	for k,v in pairs(t) do
		if type(v)=="table" then r[k]=cloneTable(v) else r[k]=v end
	end
	return r
end

local function roundToStep(x, step)
	step = step or 1
	return math.floor((x/step)+0.5)*step
end

local function safe_pcall(f, ...)
	local ok, res = pcall(f, ...)
	if not ok then
		warn("[OrionX] ".. tostring(res))
		return nil, res
	end
	return res
end

-- ======== Pure Lua SHA-256 (for BuildInfo and runtime self-checks) ========
-- Compact SHA-256 implementation (public domain / CC0 inspired)
local function rshift(x,n) return math.floor(x/2^n) end
local function band(a,b) return a & b end
local function bor(a,b) return a | b end
local function bxor(a,b) return a ~ b end
local function bnot(a) return ~a end
local function rrotate(x,n) n=n%32; return rshift(x,n) | ((x << (32-n)) & 0xFFFFFFFF) end

local function sha256(msg)
	local H = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19}
	local K = {
		0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
		0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
		0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
		0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
		0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
		0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
		0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
		0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
	}
	local function to_bytes(s)
		local bytes = table.create(#s)
		for i=1,#s do bytes[i]=string.byte(s,i) end
		return bytes
	end
	local function u32(a,b,c,d)
		return ((a<<24) | (b<<16) | (c<<8) | d) & 0xFFFFFFFF
	end
	local bytes = to_bytes(msg)
	local bitlen = #bytes * 8
	table.insert(bytes, 0x80)
	while (#bytes % 64) ~= 56 do table.insert(bytes, 0) end
	local len = bitlen
	local lenBytes = {}
	for i=1,8 do lenBytes[9-i] = len & 0xFF; len = rshift(len,8) end
	for i=1,8 do table.insert(bytes, lenBytes[i]) end

	for i=1,#bytes,64 do
		local w = table.create(64,0)
		for j=0,15 do
			local b1=bytes[i + j*4]; local b2=bytes[i + j*4 + 1]; local b3=bytes[i + j*4 + 2]; local b4=bytes[i + j*4 + 3]
			w[j+1] = u32(b1,b2,b3,b4)
		end
		for j=17,64 do
			local v = w[j-15]
			local s0 = bxor(bxor(rrotate(v,7), rrotate(v,18)), rshift(v,3))
			v = w[j-2]
			local s1 = bxor(bxor(rrotate(v,17), rrotate(v,19)), rshift(v,10))
			w[j] = (w[j-16] + s0 + w[j-7] + s1) & 0xFFFFFFFF
		end
		local a,b,c,d,e,f,g,h = table.unpack(H)
		for j=1,64 do
			local S1 = bxor(bxor(rrotate(e,6), rrotate(e,11)), rrotate(e,25))
			local ch = bxor(band(e,f), band(bnot(e),g))
			local temp1 = (h + S1 + ch + K[1][j] + w[j]) & 0xFFFFFFFF
			local S0 = bxor(bxor(rrotate(a,2), rrotate(a,13)), rrotate(a,22))
			local maj = bxor(bxor(band(a,b), band(a,c)), band(b,c))
			local temp2 = (S0 + maj) & 0xFFFFFFFF
			h = g; g = f; f = e
			d = (d + temp1) & 0xFFFFFFFF
			e = d
			c = b; b = a
			a = (temp1 + temp2) & 0xFFFFFFFF
		end
		H[1] = (H[1] + a) & 0xFFFFFFFF
		H[2] = (H[2] + b) & 0xFFFFFFFF
		H[3] = (H[3] + c) & 0xFFFFFFFF
		H[4] = (H[4] + d) & 0xFFFFFFFF
		H[5] = (H[5] + e) & 0xFFFFFFFF
		H[6] = (H[6] + f) & 0xFFFFFFFF
		H[7] = (H[7] + g) & 0xFFFFFFFF
		H[8] = (H[8] + h) & 0xFFFFFFFF
	end
	return string.format("%08x%08x%08x%08x%08x%08x%08x%08x", H[1],H[2],H[3],H[4],H[5],H[6],H[7],H[8])
end

-- ======== Signal / Observer ========
local function createSignal()
	local sig = {}
	sig._binds = {}
	function sig:Connect(fn)
		assert(type(fn)=="function","Signal.Connect expects function")
		local c = {fn=fn, connected=true}
		self._binds[c]=true
		return {
			Disconnect=function()
				c.connected=false; self._binds[c]=nil
			end
		}
	end
	function sig:Once(fn)
		local con; con = self:Connect(function(...)
			con.Disconnect()
			fn(...)
		end)
		return con
	end
	function sig:Fire(...)
		for c,_ in pairs(self._binds) do
			if c.connected then
				local ok,err=pcall(c.fn,...)
				if not ok then warn("[OrionX.Signal] "..tostring(err)) end
			end
		end
	end
	function sig:DisconnectAll()
		for c,_ in pairs(self._binds) do c.connected=false end
		table.clear(self._binds)
	end
	return sig
end

-- ======== Storage Strategy ========
local Storage = {}
Storage.__index = Storage
function Storage.new(baseDir)
	local self = setmetatable({}, Storage)
	self.baseDir = baseDir or "orionx"
	return self
end
function Storage:_safe(path)
	path = tostring(path or "")
	path = path:gsub("[^%w_%-/%.]","_")
	return (self.baseDir.."/"..path):gsub("//+","/")
end
function Storage:_exists(f)
	if typeofx(isfile)=="function" then
		local ok, res = pcall(isfile, f)
		return ok and res or false
	end
	return false
end
function Storage:write(path, data)
	local p = self:_safe(path)
	if typeofx(writefile)=="function" then
		local ok,err = pcall(writefile, p, data)
		if not ok then warn("[OrionX.Storage] "..tostring(err)) end
		return ok
	end
	return false
end
function Storage:read(path)
	local p = self:_safe(path)
	if typeofx(readfile)=="function" then
		local ok,res = pcall(readfile, p)
		return ok and res or nil
	end
	return nil
end
function Storage:list(dir)
	dir = self:_safe(dir or "")
	if typeofx(listfiles)=="function" then
		local ok,res = pcall(listfiles, dir)
		return ok and res or {}
	end
	return {}
end

-- ======== Theme Strategy ========
local ThemeSchema = {
	Background = "Color3",
	Foreground = "Color3",
	Accent = "Color3",
	AccentMuted = "Color3",
	Stroke = "Color3",
	StrokeStrong = "Color3",
	Text = "Color3",
	TextDim = "Color3",
	Section = "Color3",
	SectionHover = "Color3",
	Button = "Color3",
	ButtonHover = "Color3",
	ToggleOn = "Color3",
	ToggleOff = "Color3",
	SliderTrack = "Color3",
	SliderFill = "Color3",
	Dropdown = "Color3",
	DropdownItem = "Color3",
	Input = "Color3",
	NotificationBg = "Color3",
	Error = "Color3",
	Success = "Color3",
	Warning = "Color3",
	Info = "Color3",
	ContrastHighText = "Color3",
	ContrastHighBg = "Color3",
}

local DefaultTheme = {
	Background = Color3.fromRGB(18,18,20),
	Foreground = Color3.fromRGB(26,26,28),
	Accent = Color3.fromRGB(38,132,255),
	AccentMuted = Color3.fromRGB(24,90,180),
	Stroke = Color3.fromRGB(40,40,45),
	StrokeStrong = Color3.fromRGB(60,60,65),
	Text = Color3.fromRGB(230,230,235),
	TextDim = Color3.fromRGB(180,180,185),
	Section = Color3.fromRGB(24,24,26),
	SectionHover = Color3.fromRGB(30,30,34),
	Button = Color3.fromRGB(36,36,40),
	ButtonHover = Color3.fromRGB(46,46,52),
	ToggleOn = Color3.fromRGB(32,180,120),
	ToggleOff = Color3.fromRGB(140,140,145),
	SliderTrack = Color3.fromRGB(50,50,56),
	SliderFill = Color3.fromRGB(38,132,255),
	Dropdown = Color3.fromRGB(30,30,34),
	DropdownItem = Color3.fromRGB(36,36,40),
	Input = Color3.fromRGB(26,26,30),
	NotificationBg = Color3.fromRGB(16,16,18),
	Error = Color3.fromRGB(220,70,70),
	Success = Color3.fromRGB(60,200,120),
	Warning = Color3.fromRGB(240,180,60),
	Info = Color3.fromRGB(86,156,214),
	ContrastHighText = Color3.fromRGB(255,255,255),
	ContrastHighBg = Color3.fromRGB(0,0,0),
}

local function validateTheme(t)
	for k, typ in pairs(ThemeSchema[1]) do
		if t[k] ~= nil then
			if typ=="Color3" and typeofx(t[k])~="Color3" then
				error("Theme key "..k.." must be Color3")
			end
		end
	end
end

-- ======== Input Adapter Strategy ========
local InputAdapter = {}
InputAdapter.__index = InputAdapter
function InputAdapter.new()
	local self = setmetatable({}, InputAdapter)
	self._connections = {}
	return self
end
function InputAdapter:Connect(obj, eventName, fn)
	local con = obj[eventName]:Connect(fn)
	table.insert(self._connections, con)
	return con
end
function InputAdapter:DisconnectAll()
	for _,c in ipairs(self._connections) do
		pcall(function() c:Disconnect() end)
	end
	table.clear(self._connections)
end

-- ======== Core Singleton ========
local Core = {
	Runtime = nil
}
function Core:GetRuntime()
	if self.Runtime then return self.Runtime end
	local rt = {
		windows = {},
		renderHandlers = {},
		renderConn = nil,
		storage = Storage.new("orionx"),
		input = InputAdapter.new(),
		theme = cloneTable(DefaultTheme[1]),
		rootParent = nil,
		toggleKey = Enum.KeyCode.RightControl,
	}
	-- choose parent
	do
		local ok,coreGui = pcall(function() return game:GetService("CoreGui") end)
		if ok and coreGui then rt.rootParent = coreGui else
			local plr = Players.LocalPlayer
			if plr then
				local pgui = safe_pcall(function() return plr:WaitForChild("PlayerGui", 2) end)
				if pgui then rt.rootParent = pgui end
			end
		end
	end
	self.Runtime = rt
	return rt
end

local function ensureScreenGui(rt)
	if rt.screenGui and rt.screenGui.Parent then return rt.screenGui end
	local sg = Instance.new("ScreenGui")
	sg.Name = "OrionX"
	sg.IgnoreGuiInset = true
	sg.ResetOnSpawn = false
	sg.ZIndexBehavior = Enum.ZIndexBehavior.Global
	sg.Parent = rt.rootParent or game:GetService("CoreGui")
	rt.screenGui = sg
	return sg
end

local function startRenderLoop(rt)
	if rt.renderConn then return end
	rt.renderConn = RunService.RenderStepped:Connect(function(dt)
		for id,fn in pairs(rt.renderHandlers) do
			local ok,err = pcall(fn, dt)
			if not ok then
				warn("[OrionX.Render] "..tostring(err))
				rt.renderHandlers[id] = nil
			end
		end
	end)
end

local function stopRenderLoop(rt)
	if not rt.renderConn then return end
	local active = 0
	for _ in pairs(rt.renderHandlers) do active=active+1 end
	if active==0 then
		rt.renderConn:Disconnect()
		rt.renderConn = nil
	end
end

-- ======== UI Builders and Factory ========
local UI = {}
UI.__index = UI

local function createFrame(props)
	local f = Instance.new("Frame")
	f.BackgroundColor3 = props.Color or Color3.fromRGB(255,0,0)
	f.BorderSizePixel = 0
	f.Size = props.Size or UDim2.new(0,100,0,100)
	f.Position = props.Position or UDim2.new(0,0,0,0)
	f.Name = props.Name or "Frame"
	f.Parent = props.Parent
	return f
end

local function createText(props)
	local t = Instance.new("TextLabel")
	t.BackgroundTransparency = 1
	t.Font = Enum.Font.Gotham
	t.TextSize = props.TextSize or 14
	t.TextColor3 = props.Color or Color3.new(1,1,1)
	t.Text = props.Text or ""
	t.TextXAlignment = props.XAlign or Enum.TextXAlignment.Left
	t.TextYAlignment = props.YAlign or Enum.TextYAlignment.Center
	t.Size = props.Size or UDim2.new(1, -10, 0, 20)
	t.Position = props.Position or UDim2.new(0, 5, 0, 0)
	t.Name = props.Name or "Text"
	t.Parent = props.Parent
	return t
end

local function uiStroke(parent, color, thickness)
	local s = Instance.new("UIStroke")
	s.Thickness = thickness or 1
	s.Color = color
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = parent
	return s
end

local function uiCorner(parent, r)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, r or 6)
	c.Parent = parent
	return c
end

local function uiList(parent, padding)
	local l = Instance.new("UIListLayout")
	l.FillDirection = Enum.FillDirection.Vertical
	l.Padding = UDim.new(0, padding or 6)
	l.HorizontalAlignment = Enum.HorizontalAlignment.Left
	l.SortOrder = Enum.SortOrder.LayoutOrder
	l.Parent = parent
	return l
end

local function uiPadding(parent, pad)
	local p = Instance.new("UIPadding")
	pad = pad or 8
	p.PaddingTop = UDim.new(0,pad)
	p.PaddingBottom = UDim.new(0,pad)
	p.PaddingLeft = UDim.new(0,pad)
	p.PaddingRight = UDim.new(0,pad)
	p.Parent = parent
	return p
end

-- ======== Controls Factory ========
local ControlsFactory = {}

-- Utility: ID map and state per window
local function newState()
	return {
		idMap = {},
		values = {},
	}
end

-- Helper to map control id to object for O(1)
local function registerControl(win, id, obj)
	if id then win._state.idMap[id]=obj end
end
local function getControl(win, id) return win._state.idMap[id] end

-- Virtualized list pool for dropdown items
local function newItemPool(createFn)
	local pool = {free={}, used={}
		function pool:acquire()
			local item = table.remove(self.free) or createFn()
			table.insert(self.used, item)
			return item
		end
		function pool:releaseAll()
			for _,it in ipairs(self.used) do it.Visible=false; table.insert(self.free, it) end
			table.clear(self.used)
		end
		return pool
end

-- Common validation helpers
local function expectType(name, val, typ, optional)
	if val==nil and optional then return end
	if typeofx(val)~=typ then error(name.." must be "..typ) end
end

-- ======== Window / Tab / Section classes ========
local Window = {}; Window.__index=Window
local Tab = {}; Tab.__index=Tab
local Section = {}; Section.__index=Section

function OrionX.MakeWindow(opts)
	opts = opts or {}
	expectType("opts", opts, "table", true)
	local rt = Core:GetRuntime()
	local sg = ensureScreenGui(rt)
	startRenderLoop(rt)

	local theme = rt.theme
	-- Root window
	local main = createFrame{Parent=sg, Name="Window", Color=theme.Background, Size=UDim2.new(0, 560, 0, 420), Position=UDim2.new(0.5,-280,0.5,-210)}
	uiCorner(main, 10); uiStroke(main, theme.StrokeStrong, 1)
	local titleBar = createFrame{Parent=main, Name="TitleBar", Color=theme.Foreground, Size=UDim2.new(1,0,0,36)}
	uiCorner(titleBar, 10); uiStroke(titleBar, theme.Stroke, 1)
	local title = createText{Parent=titleBar, Text=opts.Name or "OrionX", TextSize=16, Color=theme.Text, Size=UDim2.new(1,-80,1,-0), Position=UDim2.new(0,12,0,0)}
	local closeBtn = Instance.new("TextButton"); closeBtn.Text="✕"; closeBtn.Font=Enum.Font.GothamBold; closeBtn.TextSize=16; closeBtn.AutoButtonColor=false
	closeBtn.BackgroundColor3=theme.Button; closeBtn.TextColor3=theme.Text; closeBtn.Size=UDim2.new(0,32,0,24); closeBtn.Position=UDim2.new(1,-40,0,6); closeBtn.Parent=titleBar
	uiCorner(closeBtn,6); uiStroke(closeBtn, theme.Stroke, 1)

	local leftTabs = createFrame{Parent=main, Name="Tabs", Color=theme.Foreground, Size=UDim2.new(0,160,1,-36), Position=UDim2.new(0,0,0,36)}
	uiStroke(leftTabs, theme.Stroke,1); uiPadding(leftTabs,8); local tabsList = uiList(leftTabs,6)

	local rightHolder = createFrame{Parent=main, Name="Holder", Color=theme.Background, Size=UDim2.new(1,-160,1,-36), Position=UDim2.new(0,160,0,36)}
	uiPadding(rightHolder,10)

	local tabsContent = Instance.new("Folder"); tabsContent.Name="TabsContent"; tabsContent.Parent = rightHolder

	local dragging=false; local dragStart; local startPos
	titleBar.InputBegan:Connect(function(input)
		if input.UserInputType == Enum.UserInputType.MouseButton1 then
			dragging=true; dragStart=input.Position; startPos=main.Position
			input.Changed:Connect(function()
				if input.UserInputState==Enum.UserInputState.End then dragging=false end
			end)
		end
	end)
	UserInputService.InputChanged:Connect(function(input)
		if dragging and input.UserInputType==Enum.UserInputType.MouseMovement then
			local delta = input.Position - dragStart
			main.Position = UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
		end
	end)

	closeBtn.MouseButton1Click:Connect(function()
		main.Visible=false
	end)

	local win = setmetatable({
		_rt = rt,
		_root = main,
		_tabsFolder = tabsContent,
		_tabsList = tabsList,
		_tabsLeft = leftTabs,
		_state = newState(),
		_theme = theme,
		_visible = true,
	}, Window)

	function win:SetTheme(t)
		expectType("theme", t, "table")
		validateTheme(t)
		deepMerge(self._rt.theme, t)
		-- basic repaint
		main.BackgroundColor3=self._rt.theme.Background
		titleBar.BackgroundColor3=self._rt.theme.Foreground
		closeBtn.BackgroundColor3=self._rt.theme.Button
		leftTabs.BackgroundColor3=self._rt.theme.Foreground
		rightHolder.BackgroundColor3=self._rt.theme.Background
		title.TextColor3=self._rt.theme.Text
	end

	function win:SetToggleKey(keyCode)
		expectType("keyCode", keyCode, "EnumItem")
		self._rt.toggleKey = keyCode
	end

	function win:AddTab(optsTab)
		optsTab = optsTab or {}
		local tbtn = Instance.new("TextButton")
		tbtn.Size = UDim2.new(1,-4,0,28)
		tbtn.BackgroundColor3 = theme.Button
		tbtn.TextColor3 = theme.Text
		tbtn.Text = (optsTab.Name or "Tab")
		tbtn.Font = Enum.Font.Gotham
		tbtn.TextSize = 14
		tbtn.AutoButtonColor = false
		tbtn.Parent = leftTabs
		uiCorner(tbtn,6); uiStroke(tbtn, theme.Stroke, 1)

		local page = createFrame{Parent=tabsContent, Name=optsTab.Name or "Tab", Color=theme.Background, Size=UDim2.new(1, -10, 1, -10), Position=UDim2.new(0,5,0,5)}
		local scroll = Instance.new("ScrollingFrame")
		scroll.Size = UDim2.new(1,0,1,0)
		scroll.CanvasSize=UDim2.new(0,0,0,0)
		scroll.ScrollBarThickness=6
		scroll.BackgroundTransparency=1
		scroll.Parent=page
		uiPadding(scroll,6); local list = uiList(scroll, 8)

		for _,child in ipairs(tabsContent:GetChildren()) do child.Visible=false end
		page.Visible=true
		tbtn.MouseButton1Click:Connect(function()
			for _,child in ipairs(tabsContent:GetChildren()) do child.Visible=false end
			page.Visible=true
		end)

		local tab = setmetatable({
			_win = win,
			_page = page,
			_scroll = scroll,
			_list = list,
		}, Tab)

		function tab:AddSection(optsSec)
			optsSec = optsSec or {}
			local sec = createFrame{Parent=scroll, Name=optsSec.Name or "Section", Color=theme.Foreground, Size=UDim2.new(1, -6, 0, 10)}
			uiCorner(sec,8); uiStroke(sec, theme.Stroke, 1); uiPadding(sec,8); local l = uiList(sec,6)
			local titleLbl
			if optsSec.Name then
				titleLbl = createText{Parent=sec, Text=optsSec.Name, TextSize=14, Color=theme.TextDim}
			end
			local body = Instance.new("Frame"); body.BackgroundTransparency=1; body.Size=UDim2.new(1,0,0,0); body.Parent=sec
			local bl = uiList(body,6)

			local section = setmetatable({
				_tab = tab,
				_sec = sec,
				_body = body,
				_list = bl,
				_pool = newItemPool(function()
					local f = Instance.new("Frame"); f.BackgroundTransparency=1; f.Size=UDim2.new(1,0,0,28); f.Visible=true; f.Parent=body; return f
				end)
			}, Section)

			-- Auto-resize
			local function resize()
				sec.Size = UDim2.new(1, -6, 0, math.max(40, body.UIListLayout.AbsoluteContentSize.Y + (titleLbl and 28 or 14)))
				scroll.CanvasSize = UDim2.new(0,0,0, tab._list.AbsoluteContentSize.Y + 20)
			end
			sec.UIListLayout:GetPropertyChangedSignal("AbsoluteContentSize"):Connect(resize)
			body.UIListLayout:GetPropertyChangedSignal("AbsoluteContentSize"):Connect(resize)
			resize()

			return section
		end

		return tab
	end

	function win:Notify(optsN)
		optsN = optsN or {}
		local duration = tonumber(optsN.Time) or 3
		local msg = tostring(optsN.Content or optsN.Message or "Notification")
		local panel = createFrame{Parent=self._rt.screenGui or ensureScreenGui(self._rt), Name="Notify", Color=self._rt.theme.NotificationBg, Size=UDim2.new(0, 280, 0, 60), Position=UDim2.new(1, -300, 0, 20)}
		uiCorner(panel, 8); uiStroke(panel, self._rt.theme.Stroke, 1)
		local t = createText{Parent=panel, Text=msg, TextSize=14, Color=self._rt.theme.Text, Size=UDim2.new(1,-12,1,-12), Position=UDim2.new(0,6,0,6)}
		panel.BackgroundTransparency=0.1
		TweenService:Create(panel, TweenInfo.new(0.15), {Position=UDim2.new(1, -300, 0, 20), BackgroundTransparency=0}):Play()
		task.delay(duration, function()
			if panel and panel.Parent then
				TweenService:Create(panel, TweenInfo.new(0.2), {BackgroundTransparency=1}):Play()
				task.delay(0.25, function() if panel then panel:Destroy() end end)
			end
		end)
	end

	function win:Destroy()
		-- disconnect render handlers owned by this window
		for id,_ in pairs(self._rt.renderHandlers) do
			if tostring(id):find(tostring(self)) then
				self._rt.renderHandlers[id]=nil
			end
		end
		if self._root then self._root:Destroy() end
		table.clear(self._state.idMap)
		table.clear(self._state.values)
		stopRenderLoop(self._rt)
	end

	-- global visibility toggle
	UserInputService.InputBegan:Connect(function(inp, gpe)
		if gpe then return end
		if inp.KeyCode == rt.toggleKey then
			main.Visible = not main.Visible
		end
	end)

	table.insert(rt.windows, win)
	return win
end

-- ======== Section controls ========
function Section:_addBaseRow(height)
	local row = Instance.new("Frame")
	row.BackgroundColor3 = self._tab._win._rt.theme.Section
	row.Size = UDim2.new(1,0,0,height or 28)
	row.Parent = self._body
	uiCorner(row,6); uiStroke(row, self._tab._win._rt.theme.Stroke, 1)
	local label = createText{Parent=row, Text="", TextSize=14, Color=self._tab._win._rt.theme.Text, Size=UDim2.new(0.5,-8,1,-0), Position=UDim2.new(0,8,0,0)}
	return row, label
end

function Section:AddLabel(text)
	local row = Instance.new("TextLabel")
	row.BackgroundTransparency=1
	row.Font=Enum.Font.Gotham
	row.TextSize=14
	row.TextColor3=self._tab._win._rt.theme.Text
	row.TextXAlignment=Enum.TextXAlignment.Left
	row.Text = tostring(text or "")
	row.Size=UDim2.new(1, -12, 0, 22)
	row.Position=UDim2.new(0,6,0,0)
	row.Parent=self._body
	return {Object=row, Destroy=function() row:Destroy() end}
end

function Section:AddParagraph(title, text)
	local row = Instance.new("Frame"); row.BackgroundColor3=self._tab._win._rt.theme.Section; row.Parent=self._body; row.Size=UDim2.new(1,0,0,72)
	uiCorner(row,6); uiStroke(row, self._tab._win._rt.theme.Stroke,1)
	local t1 = createText{Parent=row, Text=tostring(title or ""), TextSize=14, Color=self._tab._win._rt.theme.Text}
	t1.Position=UDim2.new(0,8,0,6); t1.Size=UDim2.new(1,-16,0,20)
	local t2 = createText{Parent=row, Text=tostring(text or ""), TextSize=13, Color=self._tab._win._rt.theme.TextDim}
	t2.Position=UDim2.new(0,8,0,28); t2.Size=UDim2.new(1,-16,0,38); t2.TextXAlignment=Enum.TextXAlignment.Left
	t2.TextWrapped=true
	return {Object=row, Destroy=function() row:Destroy() end}
end

function Section:AddSeparator()
	local sep = Instance.new("Frame")
	sep.BackgroundColor3 = self._tab._win._rt.theme.StrokeStrong
	sep.BorderSizePixel = 0
	sep.Size = UDim2.new(1, -12, 0, 1)
	sep.Parent = self._body
	return {Object=sep, Destroy=function() sep:Destroy() end}
end

function Section:AddButton(opts)
	opts = opts or {}
	local text = tostring(opts.Name or opts.Text or "Button")
	local cb = opts.Callback
	local row, label = self:_addBaseRow(32)
	label.Text = text
	local btn = Instance.new("TextButton"); btn.AutoButtonColor=false; btn.Text="Run"; btn.Font=Enum.Font.GothamBold; btn.TextSize=14
	btn.BackgroundColor3=self._tab._win._rt.theme.Button; btn.TextColor3=self._tab._win._rt.theme.Text
	btn.Size=UDim2.new(0,80,0,24); btn.Position=UDim2.new(1,-88,0.5,-12); btn.Parent=row
	uiCorner(btn,6); uiStroke(btn, self._tab._win._rt.theme.Stroke,1)
	local _busy=false
	btn.MouseButton1Click:Connect(function()
		if _busy then return end; _busy=true
		if type(cb)=="function" then safe_pcall(cb) end
		task.delay(0, function() _busy=false end)
	end)
	return {
		Object=row,
		Set=function(_, name) label.Text=tostring(name) end,
		Destroy=function() row:Destroy() end
	}
end

function Section:AddToggle(opts)
	opts = opts or {}
	local text = tostring(opts.Name or "Toggle")
	local def = opts.Default == true
	local cb = opts.Callback
	local row, label = self:_addBaseRow(32)
	label.Text = text
	local box = Instance.new("Frame"); box.Size=UDim2.new(0,36,0,20); box.Position=UDim2.new(1,-48,0.5,-10)
	box.BackgroundColor3 = def and self._tab._win._rt.theme.ToggleOn or self._tab._win._rt.theme.ToggleOff
	box.Parent=row; uiCorner(box,10); uiStroke(box, self._tab._win._rt.theme.Stroke,1)
	local knob = createFrame{Parent=box, Color=self._tab._win._rt.theme.Foreground, Size=UDim2.new(0,16,0,16), Position=UDim2.new(0,2,0,2)}; uiCorner(knob,8)
	if def then knob.Position=UDim2.new(1,-18,0,2) end
	local value = def
	local _busy=false
	local function apply(v)
		value=v
		TweenService:Create(knob, TweenInfo.new(0.1), {Position=v and UDim2.new(1,-18,0,2) or UDim2.new(0,2,0,2)}):Play()
		TweenService:Create(box, TweenInfo.new(0.1), {BackgroundColor3=v and self._tab._win._rt.theme.ToggleOn or self._tab._win._rt.theme.ToggleOff}):Play()
	end
	box.InputBegan:Connect(function(inp)
		if inp.UserInputType==Enum.UserInputType.MouseButton1 then
			if _busy then return end; _busy=true
			apply(not value)
			if type(cb)=="function" then safe_pcall(cb, value) end
			task.delay(0, function() _busy=false end)
		end
	end)
	return {
		Object=row,
		Get=function() return value end,
		Set=function(_, v) apply(v==true) end,
		Destroy=function() row:Destroy() end
	}
end

function Section:AddSlider(opts)
	opts = opts or {}
	local text = tostring(opts.Name or "Slider")
	local min = tonumber(opts.Min) or 0
	local max = tonumber(opts.Max) or 100
	local step = tonumber(opts.Increment or opts.Step) or 1
	local def = tonumber(opts.Default) or min
	local cb = opts.Callback
	local row, label = self:_addBaseRow(36)
	label.Text = string.format("%s: %s", text, def)
	local track = createFrame{Parent=row, Color=self._tab._win._rt.theme.SliderTrack, Size=UDim2.new(0,220,0,6), Position=UDim2.new(1,-240,0.5,-3)}; uiCorner(track,3)
	local fill = createFrame{Parent=track, Color=self._tab._win._rt.theme.SliderFill, Size=UDim2.new(0,0,1,0)}; uiCorner(fill,3)
	local dragging=false
	local value = def
	local function setFromX(x)
		local rel = math.clamp((x - track.AbsolutePosition.X) / track.AbsoluteSize.X, 0, 1)
		local raw = min + rel*(max-min)
		local v = math.clamp(roundToStep(raw, step), min, max)
		value = v
		fill.Size = UDim2.new((v-min)/(max-min),0,1,0)
		label.Text = string.format("%s: %s", text, v)
		if type(cb)=="function" then safe_pcall(cb, v) end
	end
	track.InputBegan:Connect(function(inp)
		if inp.UserInputType==Enum.UserInputType.MouseButton1 then
			dragging=true; setFromX(inp.Position.X)
			inp.Changed:Connect(function() if inp.UserInputState==Enum.UserInputState.End then dragging=false end end)
		end
	end)
	UserInputService.InputChanged:Connect(function(inp)
		if dragging and inp.UserInputType==Enum.UserInputType.MouseMovement then setFromX(inp.Position.X) end
	end)
	-- init
	fill.Size = UDim2.new((def-min)/math.max(1,(max-min)),0,1,0)
	return {
		Object=row,
		Get=function() return value end,
		Set=function(_, v) if type(v)=="number" then setFromX(track.AbsolutePosition.X + ((v-min)/(max-min))*track.AbsoluteSize.X) end end,
		Destroy=function() row:Destroy() end
	}
end

function Section:AddDropdown(opts)
	opts = opts or {}
	local text = tostring(opts.Name or "Dropdown")
	local list = opts.Options or opts.List or {}
	local def = opts.Default
	local cb = opts.Callback
	local row, label = self:_addBaseRow(32)
	label.Text = text
	local btn = Instance.new("TextButton"); btn.Size=UDim2.new(0,180,0,24); btn.Position=UDim2.new(1,-188,0.5,-12)
	btn.Text = def and tostring(def) or "Select"
	btn.Font=Enum.Font.Gotham; btn.TextSize=14; btn.AutoButtonColor=false
	btn.BackgroundColor3=self._tab._win._rt.theme.Dropdown; btn.TextColor3=self._tab._win._rt.theme.Text; btn.Parent=row
	uiCorner(btn,6); uiStroke(btn, self._tab._win._rt.theme.Stroke,1)

	local listFrame = createFrame{Parent=row, Name="List", Color=self._tab._win._rt.theme.Dropdown, Size=UDim2.new(0,180,0,0), Position=UDim2.new(1,-188,0,28)}
	uiCorner(listFrame,6); uiStroke(listFrame, self._tab._win._rt.theme.Stroke,1); listFrame.Visible=false
	local sf = Instance.new("ScrollingFrame"); sf.Size=UDim2.new(1,0,1,0); sf.CanvasSize=UDim2.new(0,0,0,0); sf.ScrollBarThickness=6; sf.BackgroundTransparency=1; sf.Parent=listFrame
	local lay = uiList(sf,4); uiPadding(sf,6)

	local pool = newItemPool(function()
		local b = Instance.new("TextButton"); b.Size=UDim2.new(1, -4, 0, 24); b.AutoButtonColor=false
		b.BackgroundColor3=self._tab._win._rt.theme.DropdownItem; b.TextColor3=self._tab._win._rt.theme.Text; b.Font=Enum.Font.Gotham; b.TextSize=14
		uiCorner(b,4); uiStroke(b, self._tab._win._rt.theme.Stroke,1); b.Parent=sf; return b
	end)

	local value = def
	local function setOptions(items)
		pool:releaseAll()
		for _,name in ipairs(items) do
			local b = pool:acquire(); b.Visible=true; b.Text=tostring(name)
			b.MouseButton1Click:Connect(function()
				value = name; btn.Text = tostring(name); listFrame.Visible=false
				if type(cb)=="function" then safe_pcall(cb, name) end
			end)
		end
		sf.CanvasSize = UDim2.new(0,0,0, math.min(#items*28 + 12, 180))
		listFrame.Size = UDim2.new(0,180,0, math.min(#items*28 + 12, 180))
	end
	setOptions(list)

	btn.MouseButton1Click:Connect(function()
		listFrame.Visible = not listFrame.Visible
	end)

	return {
		Object=row,
		Get=function() return value end,
		Set=function(_, v) value=v; btn.Text=tostring(v) end,
		Refresh=function(_, items) setOptions(items or {}) end,
		Destroy=function() row:Destroy() end
	}
end

function Section:AddTextbox(opts)
	opts = opts or {}
	local text = tostring(opts.Name or "Textbox")
	local def = tostring(opts.Default or "")
	local cb = opts.Callback
	local row, label = self:_addBaseRow(32); label.Text = text
	local box = Instance.new("TextBox"); box.Text=def; box.PlaceholderText=opts.Placeholder or ""; box.Font=Enum.Font.Gotham; box.TextSize=14
	box.BackgroundColor3=self._tab._win._rt.theme.Input; box.TextColor3=self._tab._win._rt.theme.Text
	box.Size=UDim2.new(0,220,0,24); box.Position=UDim2.new(1,-228,0.5,-12); box.Parent=row
	uiCorner(box,6); uiStroke(box, self._tab._win._rt.theme.Stroke,1)
	box.FocusLost:Connect(function(enter)
		if type(cb)=="function" then safe_pcall(cb, box.Text) end
	end)
	return {
		Object=row,
		Get=function() return box.Text end,
		Set=function(_, v) box.Text=tostring(v or "") end,
		Destroy=function() row:Destroy() end
	}
end

function Section:AddBind(opts)
	opts = opts or {}
	local text = tostring(opts.Name or "Bind")
	local def = opts.Default or Enum.KeyCode.None
	local cb = opts.Callback
	local row, label = self:_addBaseRow(32); label.Text = text
	local btn = Instance.new("TextButton"); btn.AutoButtonColor=false; btn.Text=(def ~= Enum.KeyCode.None and def.Name or "Set"); btn.Font=Enum.Font.Gotham; btn.TextSize=14
	btn.BackgroundColor3=self._tab._win._rt.theme.Button; btn.TextColor3=self._tab._win._rt.theme.Text
	btn.Size=UDim2.new(0,120,0,24); btn.Position=UDim2.new(1,-128,0.5,-12); btn.Parent=row
	uiCorner(btn,6); uiStroke(btn, self._tab._win._rt.theme.Stroke,1)
	local waiting=false; local key = def
	btn.MouseButton1Click:Connect(function()
		waiting=true; btn.Text="Press key..."
	end)
	UserInputService.InputBegan:Connect(function(inp, gpe)
		if waiting and not gpe then
			if inp.KeyCode and inp.KeyCode ~= Enum.KeyCode.Unknown then
				key = inp.KeyCode; btn.Text = key.Name; waiting=false
				if type(cb)=="function" then safe_pcall(cb, key) end
			end
		end
	end)
	return {
		Object=row,
		Get=function() return key end,
		Set=function(_, v) if typeofx(v)=="EnumItem" then key=v; btn.Text=v.Name end end,
		Destroy=function() row:Destroy() end
	}
end

function Section:AddColorpicker(opts)
	opts = opts or {}
	local text = tostring(opts.Name or "Colorpicker")
	local def = opts.Default or Color3.fromRGB(255,255,255)
	local cb = opts.Callback
	local row, label = self:_addBaseRow(44); label.Text = text
	local preview = createFrame{Parent=row, Color=def, Size=UDim2.new(0,32,0,20), Position=UDim2.new(1,-40,0,12)}; uiCorner(preview,4); uiStroke(preview, self._tab._win._rt.theme.Stroke,1)

	-- Simple RGB sliders as a reliable cross-executor picker
	local function makeSlider(offY, labelText, init, onChange)
		local lbl = createText{Parent=row, Text=labelText, TextSize=12, Color=self._tab._win._rt.theme.TextDim, Size=UDim2.new(0,24,0,16), Position=UDim2.new(0,8,0,offY)}
		local track = createFrame{Parent=row, Color=self._tab._win._rt.theme.SliderTrack, Size=UDim2.new(0,120,0,6), Position=UDim2.new(0,40,0,offY+6)}; uiCorner(track,3)
		local fill = createFrame{Parent=track, Color=self._tab._win._rt.theme.SliderFill, Size=UDim2.new(init/255,0,1,0)}; uiCorner(fill,3)
		local dragging=false
		local function setFromX(x)
			local rel = math.clamp((x - track.AbsolutePosition.X) / track.AbsoluteSize.X, 0, 1)
			local v = math.floor(rel*255+0.5)
			fill.Size = UDim2.new(v/255,0,1,0)
			onChange(v)
		end
		track.InputBegan:Connect(function(inp)
			if inp.UserInputType==Enum.UserInputType.MouseButton1 then
				dragging=true; setFromX(inp.Position.X)
				inp.Changed:Connect(function() if inp.UserInputState==Enum.UserInputState.End then dragging=false end end)
			end
		end)
		UserInputService.InputChanged:Connect(function(inp)
			if dragging and inp.UserInputType==Enum.UserInputType.MouseMovement then setFromX(inp.Position.X) end
		end)
		return {Set=function(v) fill.Size=UDim2.new(v/255,0,1,0) end}
	end

	local r,g,b = math.floor(def.R*255+0.5), math.floor(def.G*255+0.5), math.floor(def.B*255+0.5)
	local function apply()
		local c = Color3.fromRGB(r,g,b)
		preview.BackgroundColor3 = c
		if type(cb)=="function" then safe_pcall(cb, c) end
	end
	local rs = makeSlider(2,"R", r, function(v) r=v; apply() end)
	local gs = makeSlider(20,"G", g, function(v) g=v; apply() end)
	local bs = makeSlider(38,"B", b, function(v) b=v; apply() end)

	return {
		Object=row,
		Get=function() return Color3.fromRGB(r,g,b) end,
		Set=function(_, c) if typeofx(c)=="Color3" then r=math.floor(c.R*255+0.5); g=math.floor(c.G*255+0.5); b=math.floor(c.B*255+0.5); apply(); rs.Set(r); gs.Set(g); bs.Set(b) end end,
		Destroy=function() row:Destroy() end
	}
end

-- ======== Global functions: Theme, Notify, Save/Load, Example, test_smoke ========
function OrionX.SetTheme(t) local rt=Core:GetRuntime(); validateTheme(t); deepMerge(rt.theme, t) end

function OrionX.Notify(opts) local w=Core:GetRuntime().windows[1]; if w then return w:Notify(opts) end end

-- Config IO
local function serialize(tbl) return HttpService:JSONEncode(tbl) end
local function deserialize(str) local ok,res=pcall(function() return HttpService:JSONDecode(str) end); return ok and res or nil end

function OrionX.Save(profile)
	expectType("profile", profile, "string")
	local rt = Core:GetRuntime()
	local dump = {}
	for _,w in ipairs(rt.windows) do
		dump[w._root.Name] = { Theme = rt.theme } -- extendable
	end
	local ok = rt.storage:write("profiles/"..profile..".json", serialize(dump))
	return ok
end

function OrionX.Load(profile)
	expectType("profile", profile, "string")
	local rt = Core:GetRuntime()
	local txt = rt.storage:read("profiles/"..profile..".json")
	if not txt then return false end
	local data = deserialize(txt); if not data then return false end
	if data and data.Theme then OrionX.SetTheme(data.Theme) end
	return true
end

-- ======== Build Info and self-checks ========
function OrionX.BuildInfo()
	local info = debug.getinfo(1,'S')
	local source = info and info.source or ""
	local path = source:match("^@(.+)$")
	local size, hash = nil, nil
	if path and typeofx(readfile)=="function" then
		local ok, data = pcall(readfile, path)
		if ok and data then
			size = #data
			hash = sha256(data)
		end
	end
	return {
		version = OrionX._VERSION,
		build = OrionX._BUILD_DATE,
		file = path,
		size = size,
		sha256 = hash
	}
end

-- ======== Example usage string ========
function OrionX.Example()
	return [[
-- Example usage for OrionX on executors with I/O:
local OrionX = loadstring(readfile("OrionX.lua"))()

local win = OrionX.MakeWindow({Name="OrionX Demo"})
local tab = win:AddTab({Name="Main"})
local sec = tab:AddSection({Name="Controls"})

sec:AddLabel("OrionX controls demo")
sec:AddSeparator()

sec:AddButton({Name="Click Me", Callback=function() print("Button clicked") end})

sec:AddToggle({
    Name="God Mode",
    Default=false,
    Callback=function(v) print("Toggle:", v) end
})

sec:AddSlider({
    Name="WalkSpeed",
    Min=16, Max=200, Default=16, Step=1,
    Callback=function(v) print("Slider:", v) end
})

local dd = sec:AddDropdown({
    Name="Teams",
    Options={"Red","Blue","Green"},
    Default="Red",
    Callback=function(v) print("Dropdown:", v) end
})
-- later refresh
dd:Refresh({"Red","Blue","Green","Yellow"})

sec:AddTextbox({
    Name="Chat",
    Default="Hello",
    Callback=function(txt) print("Textbox:", txt) end
})

sec:AddBind({
    Name="Trigger",
    Default=Enum.KeyCode.F,
    Callback=function(key) print("Bind:", key) end
})

sec:AddColorpicker({
    Name="Tint",
    Default=Color3.fromRGB(255,128,0),
    Callback=function(c) print("Color:", c) end
})

OrionX.SetTheme({
    Accent = Color3.fromRGB(255,120,40),
    SliderFill = Color3.fromRGB(255,120,40),
})

OrionX.Save("profile1")
OrionX.Load("profile1")

win:SetToggleKey(Enum.KeyCode.RightControl)
win:Notify({Content="Hello from OrionX", Time=3})

-- Destroy when done
-- win:Destroy()

-- Print build info with computed SHA-256 and size:
local info = OrionX.BuildInfo()
print("OrionX", info.version, info.build, info.size, info.sha256)
]]
end

-- ======== test_smoke() ========
function OrionX.test_smoke()
	local ok, err = pcall(function()
		local w = OrionX.MakeWindow({Name="Test"})
		local t = w:AddTab({Name="A"})
		local s = t:AddSection({Name="S"})
		s:AddLabel("L")
		s:AddParagraph("P","Body")
		s:AddSeparator()
		s:AddButton({Name="B", Callback=function() end})
		local tg = s:AddToggle({Name="T", Default=true, Callback=function(v) assert(type(v)=="boolean") end})
		local sl = s:AddSlider({Name="SL", Min=0,Max=10,Default=5,Step=1, Callback=function(v) assert(type(v)=="number") end})
		local dd = s:AddDropdown({Name="D", Options={"1","2"}, Default="1", Callback=function(v) assert(type(v)=="string") end})
		local tb = s:AddTextbox({Name="TB", Default="x", Callback=function(v) assert(type(v)=="string") end})
		local kb = s:AddBind({Name="K", Default=Enum.KeyCode.K, Callback=function(v) assert(typeof(v)=="EnumItem") end})
		local cp = s:AddColorpicker({Name="C", Default=Color3.fromRGB(1,2,3), Callback=function(v) assert(typeof(v)=="Color3") end})
		-- callbacks
		if tg.Get then assert(type(tg:Get())=="boolean") end
		if sl.Get then assert(type(sl:Get())=="number") end
		if dd.Get then assert(type(dd:Get())=="string") end
		if tb.Get then assert(type(tb:Get())=="string") end
		if kb.Get then assert(typeof(kb:Get())=="EnumItem") end
		if cp.Get then assert(typeof(cp:Get())=="Color3") end
		OrionX.SetTheme({Accent=Color3.fromRGB(1,2,3)})
		w:SetToggleKey(Enum.KeyCode.RightControl)
		OrionX.Save("smoke")
		OrionX.Load("smoke")
		w:Notify({Content="ok", Time=0.1})
		w:Destroy()
	end)
	return ok, err
end

return OrionX
