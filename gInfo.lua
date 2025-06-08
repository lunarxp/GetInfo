local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 33) then
					if (Enum <= 16) then
						if (Enum <= 7) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum > 0) then
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									elseif (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 2) then
									Stk[Inst[2]] = Env[Inst[3]];
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 5) then
								if (Enum > 4) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								end
							elseif (Enum == 6) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 11) then
							if (Enum <= 9) then
								if (Enum == 8) then
									Stk[Inst[2]] = #Stk[Inst[3]];
								else
									Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
								end
							elseif (Enum > 10) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 13) then
							if (Enum > 12) then
								Env[Inst[3]] = Stk[Inst[2]];
							else
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							end
						elseif (Enum <= 14) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 15) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 24) then
						if (Enum <= 20) then
							if (Enum <= 18) then
								if (Enum == 17) then
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								else
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum == 19) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum <= 22) then
							if (Enum > 21) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum == 23) then
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						end
					elseif (Enum <= 28) then
						if (Enum <= 26) then
							if (Enum > 25) then
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 3) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum == 27) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						elseif (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 30) then
						if (Enum == 29) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 31) then
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
					elseif (Enum > 32) then
						do
							return Stk[Inst[2]];
						end
					else
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 50) then
					if (Enum <= 41) then
						if (Enum <= 37) then
							if (Enum <= 35) then
								if (Enum == 34) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								end
							elseif (Enum > 36) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							end
						elseif (Enum <= 39) then
							if (Enum > 38) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum == 40) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						end
					elseif (Enum <= 45) then
						if (Enum <= 43) then
							if (Enum > 42) then
								VIP = Inst[3];
							else
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							end
						elseif (Enum == 44) then
							Stk[Inst[2]] = {};
						else
							local A = Inst[2];
							local Index = Stk[A];
							local Step = Stk[A + 2];
							if (Step > 0) then
								if (Index > Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Index < Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						end
					elseif (Enum <= 47) then
						if (Enum > 46) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 48) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					elseif (Enum > 49) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					else
						do
							return;
						end
					end
				elseif (Enum <= 59) then
					if (Enum <= 54) then
						if (Enum <= 52) then
							if (Enum > 51) then
								Env[Inst[3]] = Stk[Inst[2]];
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum == 53) then
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 56) then
						if (Enum > 55) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 57) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					elseif (Enum > 58) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 63) then
					if (Enum <= 61) then
						if (Enum > 60) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum > 62) then
						local NewProto = Proto[Inst[3]];
						local NewUvals;
						local Indexes = {};
						NewUvals = Setmetatable({}, {__index=function(_, Key)
							local Val = Indexes[Key];
							return Val[1][Val[2]];
						end,__newindex=function(_, Key, Value)
							local Val = Indexes[Key];
							Val[1][Val[2]] = Value;
						end});
						for Idx = 1, Inst[4] do
							VIP = VIP + 1;
							local Mvm = Instr[VIP];
							if (Mvm[1] == 3) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					else
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 65) then
					if (Enum == 64) then
						do
							return;
						end
					else
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 66) then
					Stk[Inst[2]] = Stk[Inst[3]];
				elseif (Enum == 67) then
					Stk[Inst[2]] = Upvalues[Inst[3]];
				else
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!623Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403073Q004C5F5374617274030B3Q0089F9548CB0DB47B6AAF44303043Q00C5DE982603043Q00D04F79C103073Q00569C2018851D26026Q00354003053Q008B8A428C2F03073Q0037C7E523C81D1C026Q00374003043Q0059EFD43503053Q0073149ABC54026Q00434003093Q00FAD6832BAEB9E1E9BD03063Q00DFB1BFED4CE103043Q007AC6A11E03073Q00DB36A9C05A305003053Q00654D2Q011B03043Q004529226003043Q0091D6DF0B03063Q004BDCA3B76A62030B3Q0033AF8E24CD21BB9932DC1003053Q00B962DAEB5703043Q00E73326C203063Q00CAAB5C4786BE03053Q0005CE2DAC7B03043Q00E849A14C03083Q0096CC765813ABD54703053Q007EDBB9223D025Q00802Q40030B3Q0024DB50664E78FAE918EB6603083Q00876CAE3E121E179303043Q009AE62BEF03083Q00A7D6894AAB78CE5303053Q00A7FF3379AA03063Q00C7EB90523D9803043Q002A03B12A03043Q004B6776D9030D3Q00EA5B7E00B112DE667503B80CC303063Q007EA7341074D903043Q00E42Q21A403073Q009CA84E40E0D47903053Q002BE1A4EA5503043Q00AE678EC503083Q007B3D6B3D284EF45303073Q009836483F58453E03093Q00D7D6E15FC7DEEB4ED503043Q003CB4A48E025Q0080434003103Q006F5F172C04E21C2Q4C0A252BE8007D6603073Q0072383E6549478D03043Q0094E6DAE003043Q00A4D889BB03053Q00FEE93096F403073Q006BB28651D2C69E03093Q003B1C8DC5B9220B90C703053Q00CA586EE2A6030D3Q00F10A91F2DEF10A95F6D8C72ABA03053Q00AAA36FE29703043Q003D3FB31C03073Q00497150D2582E5703053Q00AD23CC36B503053Q0087E14CAD7203093Q0019FFB7B3BFA7A208EC03073Q00C77A8DD8D0CCDD03133Q0080DC03E47DE49FD803F56CC4A8CA11E27CD39503063Q0096CDBD70901803043Q00098BBE6803083Q007045E4DF2C64E87103053Q00F81006F7E403073Q00E6B47F67B3D61C03093Q008F175045F75BE59E0403073Q0080EC653F26842103093Q0086AC0641BAC9CE2QA203073Q00AFCCC97124D68B03043Q006BC334F803053Q006427AC55BC03053Q008177B8A46103053Q0053CD18D9E003093Q00E5D7C23EF5DFC82FE703043Q005D86A5AD03133Q009DF3D2D636CB8177BBF5C4F03FD9B36CBAD7F903083Q001EDE92A1A25AAED203043Q00C941712E03043Q006A852E1003053Q00742F72D80803063Q00203840139C3A03093Q0059DAEA5549E88548C903073Q00E03AA885363A920008012Q0012383Q00013Q00200B5Q0002001238000100013Q00200B000100010003001238000200013Q00200B000200020004001238000300053Q0006130003000A000100010004443Q000A0001001238000300063Q00200B000400030007001238000500083Q00200B000500050009001238000600083Q00200B00060006000A00063F00073Q000100062Q00033Q00064Q00038Q00033Q00044Q00033Q00014Q00033Q00024Q00033Q00053Q00063F00080001000100012Q00033Q00074Q0042000900084Q002C000A3Q000A2Q0042000B00073Q001220000C000C3Q001220000D000D4Q003C000B000D00022Q0042000C00084Q002C000D3Q00032Q0042000E00073Q001220000F000E3Q0012200010000F4Q003C000E00100002002004000D000E00102Q0042000E00073Q001220000F00113Q001220001000124Q003C000E00100002002004000D000E00132Q0042000E00073Q001220000F00143Q001220001000154Q003C000E00100002002004000D000E00162Q002E000C000200022Q0014000A000B000C2Q0042000B00073Q001220000C00173Q001220000D00184Q003C000B000D00022Q0042000C00084Q002C000D3Q00032Q0042000E00073Q001220000F00193Q0012200010001A4Q003C000E00100002002004000D000E00102Q0042000E00073Q001220000F001B3Q0012200010001C4Q003C000E00100002002004000D000E00132Q0042000E00073Q001220000F001D3Q0012200010001E4Q003C000E00100002002004000D000E00162Q002E000C000200022Q0014000A000B000C2Q0042000B00073Q001220000C001F3Q001220000D00204Q003C000B000D00022Q0042000C00084Q002C000D3Q00032Q0042000E00073Q001220000F00213Q001220001000224Q003C000E00100002002004000D000E00102Q0042000E00073Q001220000F00233Q001220001000244Q003C000E00100002002004000D000E00132Q0042000E00073Q001220000F00253Q001220001000264Q003C000E00100002002004000D000E00272Q002E000C000200022Q0014000A000B000C2Q0042000B00073Q001220000C00283Q001220000D00294Q003C000B000D00022Q0042000C00084Q002C000D3Q00032Q0042000E00073Q001220000F002A3Q0012200010002B4Q003C000E00100002002004000D000E00102Q0042000E00073Q001220000F002C3Q0012200010002D4Q003C000E00100002002004000D000E00132Q0042000E00073Q001220000F002E3Q0012200010002F4Q003C000E00100002002004000D000E00162Q002E000C000200022Q0014000A000B000C2Q0042000B00073Q001220000C00303Q001220000D00314Q003C000B000D00022Q0042000C00084Q002C000D3Q00042Q0042000E00073Q001220000F00323Q001220001000334Q003C000E00100002002004000D000E00102Q0042000E00073Q001220000F00343Q001220001000354Q003C000E00100002002004000D000E00132Q0042000E00073Q001220000F00363Q001220001000374Q003C000E00100002002004000D000E00272Q0042000E00073Q001220000F00383Q001220001000394Q003C000E00100002002004000D000E003A2Q002E000C000200022Q0014000A000B000C2Q0042000B00073Q001220000C003B3Q001220000D003C4Q003C000B000D00022Q0042000C00084Q002C000D3Q00032Q0042000E00073Q001220000F003D3Q0012200010003E4Q003C000E00100002002004000D000E00102Q0042000E00073Q001220000F003F3Q001220001000404Q003C000E00100002002004000D000E00132Q0042000E00073Q001220000F00413Q001220001000424Q003C000E00100002002004000D000E003A2Q002E000C000200022Q0014000A000B000C2Q0042000B00073Q001220000C00433Q001220000D00444Q003C000B000D00022Q0042000C00084Q002C000D3Q00032Q0042000E00073Q001220000F00453Q001220001000464Q003C000E00100002002004000D000E00102Q0042000E00073Q001220000F00473Q001220001000484Q003C000E00100002002004000D000E00132Q0042000E00073Q001220000F00493Q0012200010004A4Q003C000E00100002002004000D000E003A2Q002E000C000200022Q0014000A000B000C2Q0042000B00073Q001220000C004B3Q001220000D004C4Q003C000B000D00022Q0042000C00084Q002C000D3Q00032Q0042000E00073Q001220000F004D3Q0012200010004E4Q003C000E00100002002004000D000E00102Q0042000E00073Q001220000F004F3Q001220001000504Q003C000E00100002002004000D000E00132Q0042000E00073Q001220000F00513Q001220001000524Q003C000E00100002002004000D000E003A2Q002E000C000200022Q0014000A000B000C2Q0042000B00073Q001220000C00533Q001220000D00544Q003C000B000D00022Q0042000C00084Q002C000D3Q00032Q0042000E00073Q001220000F00553Q001220001000564Q003C000E00100002002004000D000E00102Q0042000E00073Q001220000F00573Q001220001000584Q003C000E00100002002004000D000E00132Q0042000E00073Q001220000F00593Q0012200010005A4Q003C000E00100002002004000D000E003A2Q002E000C000200022Q0014000A000B000C2Q0042000B00073Q001220000C005B3Q001220000D005C4Q003C000B000D00022Q0042000C00084Q002C000D3Q00032Q0042000E00073Q001220000F005D3Q0012200010005E4Q003C000E00100002002004000D000E00102Q0042000E00073Q001220000F005F3Q001220001000604Q003C000E00100002002004000D000E00132Q0042000E00073Q001220000F00613Q001220001000624Q003C000E00100002002004000D000E003A2Q002E000C000200022Q0014000A000B000C2Q002E00090002000200120D0009000B4Q00313Q00013Q00023Q00023Q00026Q00F03F026Q00704002264Q002C00025Q001220000300014Q002F00045Q001220000500013Q00042A0003002100012Q003200076Q0042000800024Q0032000900014Q0032000A00024Q0032000B00034Q0032000C00044Q0042000D6Q0042000E00063Q002023000F000600012Q0028000C000F4Q001D000B3Q00022Q0032000C00034Q0032000D00044Q0042000E00014Q002F000F00014Q0027000F0006000F001009000F0001000F2Q002F001000014Q00270010000600100010090010000100100020230010001000012Q0028000D00104Q0006000C6Q001D000A3Q0002002025000A000A00022Q003E0009000A4Q003300073Q00010004290003000500012Q0032000300054Q0042000400024Q000E000300044Q001600036Q00313Q00017Q00073Q00028Q0003073Q00790BBE4712B9CB03073Q00B32654D72976DC030A3Q00C16F182739F75E12273603053Q004E9E307642026Q00F03F030C3Q007365746D6574617461626C65011F3Q001220000100014Q000C000200033Q00261C00010016000100010004443Q001600012Q004200026Q002C00043Q00022Q003200055Q001220000600023Q001220000700034Q003C00050007000200063F00063Q000100012Q00033Q00024Q00140004000500062Q003200055Q001220000600043Q001220000700054Q003C00050007000200063F00060001000100012Q00438Q00140004000500062Q0042000300043Q001220000100063Q00261C00010002000100060004443Q00020001001238000400074Q002C00056Q0042000600034Q000E000400064Q001600045Q0004443Q000200012Q00313Q00013Q00027Q0002044Q003200026Q00190002000200012Q001E000200024Q00313Q00017Q00043Q0003053Q00652Q726F7203213Q00DABF30153BC6EFEB301F76DBF4AF2D162F96EBB92B0433D5EFAE205022D7F9A72103063Q00B69BCB447056027Q004003083Q001238000300014Q003200045Q001220000500023Q001220000600034Q003C000400060002001220000500044Q000F0003000500012Q00313Q00017Q00", GetFEnv(), ...);