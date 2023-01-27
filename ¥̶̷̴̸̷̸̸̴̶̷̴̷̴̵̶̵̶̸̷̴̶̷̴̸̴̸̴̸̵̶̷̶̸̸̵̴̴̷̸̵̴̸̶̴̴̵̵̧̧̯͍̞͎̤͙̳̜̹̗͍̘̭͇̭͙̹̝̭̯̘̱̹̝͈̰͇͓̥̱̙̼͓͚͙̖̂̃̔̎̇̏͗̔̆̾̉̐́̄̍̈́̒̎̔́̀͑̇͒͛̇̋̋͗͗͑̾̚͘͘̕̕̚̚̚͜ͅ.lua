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
		if (Byte(byte, 2) == 79) then
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
		for Idx = 1, gBits32() do
			Lines[Idx] = gBits32();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local VIP = 1;
			local Top = -1;
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local function Loop()
				local Instr = Instr;
				local Proto = Proto;
				local Params = Params;
				local _R = _R;
				local Vararg = {};
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
					if (Enum <= 19) then
						if (Enum <= 9) then
							if (Enum <= 4) then
								if (Enum <= 1) then
									if (Enum == 0) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
									else
										VIP = Inst[3];
									end
								elseif (Enum <= 2) then
									Stk[Inst[2]] = #Stk[Inst[3]];
								elseif (Enum > 3) then
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
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
							elseif (Enum <= 6) then
								if (Enum == 5) then
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
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum <= 7) then
								Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
							elseif (Enum > 8) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]]();
							end
						elseif (Enum <= 14) then
							if (Enum <= 11) then
								if (Enum == 10) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								else
									Stk[Inst[2]] = Inst[3] - Stk[Inst[4]];
								end
							elseif (Enum <= 12) then
								Stk[Inst[2]] = Inst[3];
							elseif (Enum == 13) then
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
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							end
						elseif (Enum <= 16) then
							if (Enum == 15) then
								Stk[Inst[2]] = {};
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
						elseif (Enum <= 17) then
							Env[Inst[3]] = Stk[Inst[2]];
						elseif (Enum == 18) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						elseif (Inst[2] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 29) then
						if (Enum <= 24) then
							if (Enum <= 21) then
								if (Enum == 20) then
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
								else
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
										if (Mvm[1] == 26) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								end
							elseif (Enum <= 22) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							elseif (Enum > 23) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 26) then
							if (Enum == 25) then
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 27) then
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
						elseif (Enum == 28) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						elseif (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 34) then
						if (Enum <= 31) then
							if (Enum > 30) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								do
									return;
								end
							end
						elseif (Enum <= 32) then
							if (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 33) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 37) then
						if (Enum <= 35) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						elseif (Enum > 36) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
						end
					elseif (Enum <= 38) then
						Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
					elseif (Enum > 39) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					else
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
					end
					VIP = VIP + 1;
				end
			end
			A, B = _R(PCall(Loop));
			if not A[1] then
				local line = Chunk[4][VIP] or "?";
				error("Script error at [" .. line .. "]:" .. A[2]);
			else
				return Unpack(A, 2, B);
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
VMCall("LOL!113O0003063O00737472696E6703043O006368617203043O00627974652O033O0073756203053O0062697433322O033O0062697403043O0062786F7203053O007461626C6503063O00636F6E63617403063O00696E7365727403403O004142434445464748494A4B4C4D4E4F505152535455565758595A6162636465666768696A6B6C6D6E6F707172737475767778797A303132333435363738392B2F03193O00764661735364624B7776652O63565352626A696E576B774B52030A3O006C6F6164737472696E6703043O0067616D6503073O00482O7470476574033C042O0022E8493C121FF771233E3DF476172E23D25F1C3C19D75C371615FA482A0D25C776273E14F778361D3FD0671E3635FF4A180125C8470A151FD0653E0A23C6771E1923FB4C08113DC0672D0D07FB563C151CFB752D3236E6542B0D05C26E1F321BFF7F232F3FE56D263E27D94C240C38E955050935CB492D1915D57417161ADE6C2A2C0DCB5F0E0B24DC4F2B3226F969072333DC763B1D05C15C002A3BFA4D160F1BDC511F321ADA7F38290EE34E231020C37F04012EDE6B3A1632D8730D3022F47E093A12C54F171830FB68163C1BE665003621D667180D1ADD773B2130FF6500163BE65B21342FE279361A36F66D053F34DC5B031015D969232214F878072326EB6A02152DD07B213820FD4B062921D567093226F377252E34FB772A1F38F75300373CD077352C02FE47093007F452153D3EC84A262A06FC670E3D10F47A3D0B04DE713A2318D554273E20FF5C3A3018FC7C211012FE7B2D0106DF7B060E2EC66F1C1322C267370201FA7827322EE24E050F38C4440A1D3FDC5B291A19FF5F2O2139C444291C0FE7713E2B3FD66C183812FA4D191536F2740B3725FD4A021D21D7793B1F24E645271134F469082F1AFA5029163FD964370D01E37B0B1C05F46E2B0C13F451051F33E0763A1639C4743B100EC05939163DF356051723C0491A3D39F94527333CF74A050E14FB783C210FDC5728311BF370373323C448152B12D27A261220E6713D3230E26E0D150DE068023634D6532B083DDC7E281425D747382D23F377351121C5641A3C21D07906153CE56C021321C05328023BD376242B3AEB5F240F18C667091F2EFD5537143AD967261E35E572030A13D6772A3F00F57A280911D4750E3521D35C04093DDC6801291EE14E2O193EF84A3C123DFD5E282D33FA782E3734E952082B13DF552C1502FD643B2306D577191738E271173A00D8512D193AF5543D2A2ED46F0D0C3CD5581C3719E668091F20D66738363AE8481B021EC46B3A132FD26A07113CC859003D36D3562E2F31DE7A213C22C87308121DFB5526183CC74B083C1FE76A090D23FD702D2119E36A1E1016F96C152B32C8731C0222D945231F06C357073C25E2751C2938FA6F1F150DF877252D05C3783C0302C459031100DF5A090824F26A3C3130D97519210EDD470C3E14E944212F02F24C0C3136E4451C0C1EC14903093AFE491C341DC251040A3BC07F1B0D13D544060F1CF74D1F1226DB4B382325FF4823373BDB64241539DA482B090FC66D231033D57C2A3A19EB7137103BFC6C1D1302D477012C04D572250934EB45241036E65E3F0122E0552O0920DC57183822DE572O1723EB53040C22F948093234FA64033834DA58380C22D377173E2EF07316192FE87B1E353AE853381038C44F2A3623D967202F35C850240B16F96F5F183FFC0B23024EC864371802EB0F034B16F96B061F2FFF510C1639C75F01291BD3533E0E2E83041B374784550A2E13C1675D1F04EB65260D3BE2041B2220DD48230221F570062D35FF692A0E15F96B0703053O0077B13D6F7B00293O0012173O00013O0020255O0002001217000100013O002025000100010003001217000200013O002025000200020004001217000300053O0006090003000A000100010004013O000A0001001217000300063O002025000400030007001217000500083O002025000500050009001217000600083O00202500060006000A00061500073O000100062O001A3O00064O001A8O001A3O00044O001A3O00014O001A3O00024O001A3O00053O00120C0008000B3O00061500090001000100022O001A3O00074O001A3O00083O0012110009000C3O0012170009000D3O001217000A000E3O002006000A000A000F001217000C000C4O001A000D00073O00120C000E00103O00120C000F00114O0005000D000F4O0028000C3O00022O0012000D00014O0005000A000D4O002800093O00022O00080009000100012O001E3O00013O00023O00023O00026O00F03F026O00704002284O000F00025O00120C000300014O000200045O00120C000500013O00040D0003002300014O00076O001A000800026O000900016O000A00026O000B00036O000C00044O001A000D6O001A000E00063O002023000F000600012O0005000C000F4O0028000B3O00024O000C00036O000D00044O001A000E00013O002024000F000600012O0002001000014O0014000F000F0010001026000F0001000F0020240010000600012O0002001100014O00140010001000110010260010000100100020230010001000012O0005000D00104O0003000C6O0028000A3O000200201F000A000A00022O00100009000A4O000A00073O000100041B0003000500014O000300054O001A000400024O0022000300044O001C00036O001E3O00017O00283O00093O000A3O000A3O000A3O000A3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000A3O000D3O000D3O000D3O000D3O000E3O000E3O0003013O006D03063O00737472696E672O033O00737562028O00025O00408F4003043O0067737562034O0003023O00D82903043O008377114103023O000FD903083O003284982B493E4E6503013O002E03163O00FAC4F3742O4208FAC4E935031912BB9FF374580353E003073O00DFA0D610672637012A3O001217000100023O0020250001000100032O001A00025O00120C000300043O00120C000400054O0018000100040002001211000100013O00200600013O0006001217000300013O00120C000400074O00180001000400022O001A3O00013O001217000100023O0020250001000100062O001A00028O00035O00120C000400083O00120C000500094O00180003000500024O000400016O00055O00120C0006000A3O00120C0007000B4O00180005000700022O001900030003000500120C000400074O00180001000400022O001A3O00013O00200600013O000600120C0003000C3O00061500043O000100016O00014O00180001000400020020060001000100064O00035O00120C0004000D3O00120C0005000E4O0018000300050002000204000400014O00180001000400022O0021000100024O001E3O00013O00023O000A3O0003013O003D034O0003043O0066696E64026O00F03F026O001840026O00F0BF027O0040028O0003013O003103013O0030011F3O00261D3O0004000100010004013O0004000100120C000100024O0021000100023O00120C000100026O00025O0020060002000200032O001A00046O001800020004000200202400020002000400120C000300053O00120C000400043O00120C000500063O00040D0003001D00012O001A000700013O0010070008000700062O00140008000200080020240009000600040010070009000700092O00140009000200092O0027000800080009000E130008001A000100080004013O001A000100120C000800093O0006090008001B000100010004013O001B000100120C0008000A4O001900010007000800041B0003000E00012O0021000100024O001E3O00017O001F3O00153O00153O00163O00163O00183O00183O00183O00183O00183O00183O00193O00193O00193O00193O001A3O001A3O001A3O001A3O001A3O001A3O001A3O001A3O001A3O001A3O001A3O001A3O001A3O001A3O00193O001C3O001D3O00093O00026O002040034O00028O00026O00F03F2O033O0073756203013O0031027O004003063O00737472696E6703043O0063686172011D4O000200015O00262000010005000100010004013O0005000100120C000100024O0021000100023O00120C000100033O00120C000200043O00120C000300013O00120C000400043O00040D00020017000100200600063O00052O001A000800054O001A000900054O001800060009000200261D00060014000100060004013O0014000100100B00060001000500100700060007000600060900060015000100010004013O0015000100120C000600034O001600010001000600041B0002000A0001001217000200083O0020250002000200092O001A000300014O0022000200034O001C00026O001E3O00017O001D3O001E3O001E3O001E3O001F3O001F3O00213O00223O00223O00223O00223O00233O00233O00233O00233O00233O00233O00233O00233O00233O00233O00233O00233O00223O00253O00253O00253O00253O00253O00263O002A3O00113O00113O00113O00113O00113O00113O00113O00123O00123O00123O00123O00123O00133O00133O00133O00133O00133O00133O00133O00133O00133O00133O00133O00133O00133O00133O00133O00133O00143O00143O001D3O001D3O00143O001D3O001D3O001D3O001D3O001D3O00263O001D3O00263O00273O00293O00013O00013O00023O00023O00033O00033O00043O00043O00043O00043O00053O00063O00063O00073O00073O000E3O000E3O000E3O000E3O000E3O000E3O000E3O000F3O00273O00273O00273O00273O00283O00283O00283O00283O00283O00283O00283O00283O00283O00283O00283O00283O00283O00283O00", GetFEnv(), ...);
