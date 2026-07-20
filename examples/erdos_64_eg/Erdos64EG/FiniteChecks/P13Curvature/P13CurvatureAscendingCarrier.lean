import Erdos64EG.Shared.CT10P13LabelAlgebra
import StructuralExhaustion.Core.ChunkedArrayLookup

namespace Erdos64EG.Internal

/-!
# Shallow ascending carrier for node [21]

The packed curvature tables use the ascending legal thirteen-bit-code order.
The carrier is split into small literal chunks, so local kernel checks never
refilter the ambient 2^13 code universe. The thirteen feature columns are
likewise stored as whole bit-vectors; one compatibility row can consequently
be assembled using thirteen word operations.
-/

def p13AscendingCodes00 : Array P13LabelCode := #[
  BitVec.ofNat 13 1,
  BitVec.ofNat 13 2,
  BitVec.ofNat 13 3,
  BitVec.ofNat 13 4,
  BitVec.ofNat 13 6,
  BitVec.ofNat 13 8,
  BitVec.ofNat 13 9,
  BitVec.ofNat 13 12,
  BitVec.ofNat 13 16,
  BitVec.ofNat 13 17,
  BitVec.ofNat 13 18,
  BitVec.ofNat 13 19,
  BitVec.ofNat 13 24,
  BitVec.ofNat 13 25,
  BitVec.ofNat 13 32,
  BitVec.ofNat 13 33,
  BitVec.ofNat 13 34,
  BitVec.ofNat 13 35,
  BitVec.ofNat 13 36,
  BitVec.ofNat 13 38,
  BitVec.ofNat 13 48,
  BitVec.ofNat 13 49,
  BitVec.ofNat 13 50,
  BitVec.ofNat 13 51,
  BitVec.ofNat 13 64,
  BitVec.ofNat 13 66,
  BitVec.ofNat 13 68,
  BitVec.ofNat 13 70,
  BitVec.ofNat 13 72,
  BitVec.ofNat 13 76,
  BitVec.ofNat 13 96,
  BitVec.ofNat 13 98
]

@[simp] theorem p13AscendingCodes00_size : p13AscendingCodes00.size = 32 := by
  decide

def p13AscendingCodes01 : Array P13LabelCode := #[
  BitVec.ofNat 13 100,
  BitVec.ofNat 13 102,
  BitVec.ofNat 13 128,
  BitVec.ofNat 13 129,
  BitVec.ofNat 13 132,
  BitVec.ofNat 13 136,
  BitVec.ofNat 13 137,
  BitVec.ofNat 13 140,
  BitVec.ofNat 13 144,
  BitVec.ofNat 13 145,
  BitVec.ofNat 13 152,
  BitVec.ofNat 13 153,
  BitVec.ofNat 13 192,
  BitVec.ofNat 13 196,
  BitVec.ofNat 13 200,
  BitVec.ofNat 13 204,
  BitVec.ofNat 13 256,
  BitVec.ofNat 13 257,
  BitVec.ofNat 13 258,
  BitVec.ofNat 13 259,
  BitVec.ofNat 13 264,
  BitVec.ofNat 13 265,
  BitVec.ofNat 13 272,
  BitVec.ofNat 13 273,
  BitVec.ofNat 13 274,
  BitVec.ofNat 13 275,
  BitVec.ofNat 13 280,
  BitVec.ofNat 13 281,
  BitVec.ofNat 13 288,
  BitVec.ofNat 13 289,
  BitVec.ofNat 13 290,
  BitVec.ofNat 13 291
]

@[simp] theorem p13AscendingCodes01_size : p13AscendingCodes01.size = 32 := by
  decide

def p13AscendingCodes02 : Array P13LabelCode := #[
  BitVec.ofNat 13 304,
  BitVec.ofNat 13 305,
  BitVec.ofNat 13 306,
  BitVec.ofNat 13 307,
  BitVec.ofNat 13 384,
  BitVec.ofNat 13 385,
  BitVec.ofNat 13 392,
  BitVec.ofNat 13 393,
  BitVec.ofNat 13 400,
  BitVec.ofNat 13 401,
  BitVec.ofNat 13 408,
  BitVec.ofNat 13 409,
  BitVec.ofNat 13 512,
  BitVec.ofNat 13 513,
  BitVec.ofNat 13 514,
  BitVec.ofNat 13 515,
  BitVec.ofNat 13 516,
  BitVec.ofNat 13 518,
  BitVec.ofNat 13 528,
  BitVec.ofNat 13 529,
  BitVec.ofNat 13 530,
  BitVec.ofNat 13 531,
  BitVec.ofNat 13 544,
  BitVec.ofNat 13 545,
  BitVec.ofNat 13 546,
  BitVec.ofNat 13 547,
  BitVec.ofNat 13 548,
  BitVec.ofNat 13 550,
  BitVec.ofNat 13 560,
  BitVec.ofNat 13 561,
  BitVec.ofNat 13 562,
  BitVec.ofNat 13 563
]

@[simp] theorem p13AscendingCodes02_size : p13AscendingCodes02.size = 32 := by
  decide

def p13AscendingCodes03 : Array P13LabelCode := #[
  BitVec.ofNat 13 576,
  BitVec.ofNat 13 578,
  BitVec.ofNat 13 580,
  BitVec.ofNat 13 582,
  BitVec.ofNat 13 608,
  BitVec.ofNat 13 610,
  BitVec.ofNat 13 612,
  BitVec.ofNat 13 614,
  BitVec.ofNat 13 768,
  BitVec.ofNat 13 769,
  BitVec.ofNat 13 770,
  BitVec.ofNat 13 771,
  BitVec.ofNat 13 784,
  BitVec.ofNat 13 785,
  BitVec.ofNat 13 786,
  BitVec.ofNat 13 787,
  BitVec.ofNat 13 800,
  BitVec.ofNat 13 801,
  BitVec.ofNat 13 802,
  BitVec.ofNat 13 803,
  BitVec.ofNat 13 816,
  BitVec.ofNat 13 817,
  BitVec.ofNat 13 818,
  BitVec.ofNat 13 819,
  BitVec.ofNat 13 1024,
  BitVec.ofNat 13 1025,
  BitVec.ofNat 13 1026,
  BitVec.ofNat 13 1027,
  BitVec.ofNat 13 1028,
  BitVec.ofNat 13 1030,
  BitVec.ofNat 13 1032,
  BitVec.ofNat 13 1033
]

@[simp] theorem p13AscendingCodes03_size : p13AscendingCodes03.size = 32 := by
  decide

def p13AscendingCodes04 : Array P13LabelCode := #[
  BitVec.ofNat 13 1036,
  BitVec.ofNat 13 1056,
  BitVec.ofNat 13 1057,
  BitVec.ofNat 13 1058,
  BitVec.ofNat 13 1059,
  BitVec.ofNat 13 1060,
  BitVec.ofNat 13 1062,
  BitVec.ofNat 13 1088,
  BitVec.ofNat 13 1090,
  BitVec.ofNat 13 1092,
  BitVec.ofNat 13 1094,
  BitVec.ofNat 13 1096,
  BitVec.ofNat 13 1100,
  BitVec.ofNat 13 1120,
  BitVec.ofNat 13 1122,
  BitVec.ofNat 13 1124,
  BitVec.ofNat 13 1126,
  BitVec.ofNat 13 1152,
  BitVec.ofNat 13 1153,
  BitVec.ofNat 13 1156,
  BitVec.ofNat 13 1160,
  BitVec.ofNat 13 1161,
  BitVec.ofNat 13 1164,
  BitVec.ofNat 13 1216,
  BitVec.ofNat 13 1220,
  BitVec.ofNat 13 1224,
  BitVec.ofNat 13 1228,
  BitVec.ofNat 13 1536,
  BitVec.ofNat 13 1537,
  BitVec.ofNat 13 1538,
  BitVec.ofNat 13 1539,
  BitVec.ofNat 13 1540
]

@[simp] theorem p13AscendingCodes04_size : p13AscendingCodes04.size = 32 := by
  decide

def p13AscendingCodes05 : Array P13LabelCode := #[
  BitVec.ofNat 13 1542,
  BitVec.ofNat 13 1568,
  BitVec.ofNat 13 1569,
  BitVec.ofNat 13 1570,
  BitVec.ofNat 13 1571,
  BitVec.ofNat 13 1572,
  BitVec.ofNat 13 1574,
  BitVec.ofNat 13 1600,
  BitVec.ofNat 13 1602,
  BitVec.ofNat 13 1604,
  BitVec.ofNat 13 1606,
  BitVec.ofNat 13 1632,
  BitVec.ofNat 13 1634,
  BitVec.ofNat 13 1636,
  BitVec.ofNat 13 1638,
  BitVec.ofNat 13 2048,
  BitVec.ofNat 13 2049,
  BitVec.ofNat 13 2050,
  BitVec.ofNat 13 2051,
  BitVec.ofNat 13 2052,
  BitVec.ofNat 13 2054,
  BitVec.ofNat 13 2056,
  BitVec.ofNat 13 2057,
  BitVec.ofNat 13 2060,
  BitVec.ofNat 13 2064,
  BitVec.ofNat 13 2065,
  BitVec.ofNat 13 2066,
  BitVec.ofNat 13 2067,
  BitVec.ofNat 13 2072,
  BitVec.ofNat 13 2073,
  BitVec.ofNat 13 2112,
  BitVec.ofNat 13 2114
]

@[simp] theorem p13AscendingCodes05_size : p13AscendingCodes05.size = 32 := by
  decide

def p13AscendingCodes06 : Array P13LabelCode := #[
  BitVec.ofNat 13 2116,
  BitVec.ofNat 13 2118,
  BitVec.ofNat 13 2120,
  BitVec.ofNat 13 2124,
  BitVec.ofNat 13 2176,
  BitVec.ofNat 13 2177,
  BitVec.ofNat 13 2180,
  BitVec.ofNat 13 2184,
  BitVec.ofNat 13 2185,
  BitVec.ofNat 13 2188,
  BitVec.ofNat 13 2192,
  BitVec.ofNat 13 2193,
  BitVec.ofNat 13 2200,
  BitVec.ofNat 13 2201,
  BitVec.ofNat 13 2240,
  BitVec.ofNat 13 2244,
  BitVec.ofNat 13 2248,
  BitVec.ofNat 13 2252,
  BitVec.ofNat 13 2304,
  BitVec.ofNat 13 2305,
  BitVec.ofNat 13 2306,
  BitVec.ofNat 13 2307,
  BitVec.ofNat 13 2312,
  BitVec.ofNat 13 2313,
  BitVec.ofNat 13 2320,
  BitVec.ofNat 13 2321,
  BitVec.ofNat 13 2322,
  BitVec.ofNat 13 2323,
  BitVec.ofNat 13 2328,
  BitVec.ofNat 13 2329,
  BitVec.ofNat 13 2432,
  BitVec.ofNat 13 2433
]

@[simp] theorem p13AscendingCodes06_size : p13AscendingCodes06.size = 32 := by
  decide

def p13AscendingCodes07 : Array P13LabelCode := #[
  BitVec.ofNat 13 2440,
  BitVec.ofNat 13 2441,
  BitVec.ofNat 13 2448,
  BitVec.ofNat 13 2449,
  BitVec.ofNat 13 2456,
  BitVec.ofNat 13 2457,
  BitVec.ofNat 13 3072,
  BitVec.ofNat 13 3073,
  BitVec.ofNat 13 3074,
  BitVec.ofNat 13 3075,
  BitVec.ofNat 13 3076,
  BitVec.ofNat 13 3078,
  BitVec.ofNat 13 3080,
  BitVec.ofNat 13 3081,
  BitVec.ofNat 13 3084,
  BitVec.ofNat 13 3136,
  BitVec.ofNat 13 3138,
  BitVec.ofNat 13 3140,
  BitVec.ofNat 13 3142,
  BitVec.ofNat 13 3144,
  BitVec.ofNat 13 3148,
  BitVec.ofNat 13 3200,
  BitVec.ofNat 13 3201,
  BitVec.ofNat 13 3204,
  BitVec.ofNat 13 3208,
  BitVec.ofNat 13 3209,
  BitVec.ofNat 13 3212,
  BitVec.ofNat 13 3264,
  BitVec.ofNat 13 3268,
  BitVec.ofNat 13 3272,
  BitVec.ofNat 13 3276,
  BitVec.ofNat 13 4096
]

@[simp] theorem p13AscendingCodes07_size : p13AscendingCodes07.size = 32 := by
  decide

def p13AscendingCodes08 : Array P13LabelCode := #[
  BitVec.ofNat 13 4097,
  BitVec.ofNat 13 4098,
  BitVec.ofNat 13 4099,
  BitVec.ofNat 13 4100,
  BitVec.ofNat 13 4102,
  BitVec.ofNat 13 4104,
  BitVec.ofNat 13 4105,
  BitVec.ofNat 13 4108,
  BitVec.ofNat 13 4112,
  BitVec.ofNat 13 4113,
  BitVec.ofNat 13 4114,
  BitVec.ofNat 13 4115,
  BitVec.ofNat 13 4120,
  BitVec.ofNat 13 4121,
  BitVec.ofNat 13 4128,
  BitVec.ofNat 13 4129,
  BitVec.ofNat 13 4130,
  BitVec.ofNat 13 4131,
  BitVec.ofNat 13 4132,
  BitVec.ofNat 13 4134,
  BitVec.ofNat 13 4144,
  BitVec.ofNat 13 4145,
  BitVec.ofNat 13 4146,
  BitVec.ofNat 13 4147,
  BitVec.ofNat 13 4224,
  BitVec.ofNat 13 4225,
  BitVec.ofNat 13 4228,
  BitVec.ofNat 13 4232,
  BitVec.ofNat 13 4233,
  BitVec.ofNat 13 4236,
  BitVec.ofNat 13 4240,
  BitVec.ofNat 13 4241
]

@[simp] theorem p13AscendingCodes08_size : p13AscendingCodes08.size = 32 := by
  decide

def p13AscendingCodes09 : Array P13LabelCode := #[
  BitVec.ofNat 13 4248,
  BitVec.ofNat 13 4249,
  BitVec.ofNat 13 4352,
  BitVec.ofNat 13 4353,
  BitVec.ofNat 13 4354,
  BitVec.ofNat 13 4355,
  BitVec.ofNat 13 4360,
  BitVec.ofNat 13 4361,
  BitVec.ofNat 13 4368,
  BitVec.ofNat 13 4369,
  BitVec.ofNat 13 4370,
  BitVec.ofNat 13 4371,
  BitVec.ofNat 13 4376,
  BitVec.ofNat 13 4377,
  BitVec.ofNat 13 4384,
  BitVec.ofNat 13 4385,
  BitVec.ofNat 13 4386,
  BitVec.ofNat 13 4387,
  BitVec.ofNat 13 4400,
  BitVec.ofNat 13 4401,
  BitVec.ofNat 13 4402,
  BitVec.ofNat 13 4403,
  BitVec.ofNat 13 4480,
  BitVec.ofNat 13 4481,
  BitVec.ofNat 13 4488,
  BitVec.ofNat 13 4489,
  BitVec.ofNat 13 4496,
  BitVec.ofNat 13 4497,
  BitVec.ofNat 13 4504,
  BitVec.ofNat 13 4505,
  BitVec.ofNat 13 4608,
  BitVec.ofNat 13 4609
]

@[simp] theorem p13AscendingCodes09_size : p13AscendingCodes09.size = 32 := by
  decide

def p13AscendingCodes10 : Array P13LabelCode := #[
  BitVec.ofNat 13 4610,
  BitVec.ofNat 13 4611,
  BitVec.ofNat 13 4612,
  BitVec.ofNat 13 4614,
  BitVec.ofNat 13 4624,
  BitVec.ofNat 13 4625,
  BitVec.ofNat 13 4626,
  BitVec.ofNat 13 4627,
  BitVec.ofNat 13 4640,
  BitVec.ofNat 13 4641,
  BitVec.ofNat 13 4642,
  BitVec.ofNat 13 4643,
  BitVec.ofNat 13 4644,
  BitVec.ofNat 13 4646,
  BitVec.ofNat 13 4656,
  BitVec.ofNat 13 4657,
  BitVec.ofNat 13 4658,
  BitVec.ofNat 13 4659,
  BitVec.ofNat 13 4864,
  BitVec.ofNat 13 4865,
  BitVec.ofNat 13 4866,
  BitVec.ofNat 13 4867,
  BitVec.ofNat 13 4880,
  BitVec.ofNat 13 4881,
  BitVec.ofNat 13 4882,
  BitVec.ofNat 13 4883,
  BitVec.ofNat 13 4896,
  BitVec.ofNat 13 4897,
  BitVec.ofNat 13 4898,
  BitVec.ofNat 13 4899,
  BitVec.ofNat 13 4912,
  BitVec.ofNat 13 4913
]

@[simp] theorem p13AscendingCodes10_size : p13AscendingCodes10.size = 32 := by
  decide

def p13AscendingCodes11 : Array P13LabelCode := #[
  BitVec.ofNat 13 4914,
  BitVec.ofNat 13 4915,
  BitVec.ofNat 13 6144,
  BitVec.ofNat 13 6145,
  BitVec.ofNat 13 6146,
  BitVec.ofNat 13 6147,
  BitVec.ofNat 13 6148,
  BitVec.ofNat 13 6150,
  BitVec.ofNat 13 6152,
  BitVec.ofNat 13 6153,
  BitVec.ofNat 13 6156,
  BitVec.ofNat 13 6160,
  BitVec.ofNat 13 6161,
  BitVec.ofNat 13 6162,
  BitVec.ofNat 13 6163,
  BitVec.ofNat 13 6168,
  BitVec.ofNat 13 6169,
  BitVec.ofNat 13 6272,
  BitVec.ofNat 13 6273,
  BitVec.ofNat 13 6276,
  BitVec.ofNat 13 6280,
  BitVec.ofNat 13 6281,
  BitVec.ofNat 13 6284,
  BitVec.ofNat 13 6288,
  BitVec.ofNat 13 6289,
  BitVec.ofNat 13 6296,
  BitVec.ofNat 13 6297,
  BitVec.ofNat 13 6400,
  BitVec.ofNat 13 6401,
  BitVec.ofNat 13 6402,
  BitVec.ofNat 13 6403,
  BitVec.ofNat 13 6408
]

@[simp] theorem p13AscendingCodes11_size : p13AscendingCodes11.size = 32 := by
  decide

def p13AscendingCodes12 : Array P13LabelCode := #[
  BitVec.ofNat 13 6409,
  BitVec.ofNat 13 6416,
  BitVec.ofNat 13 6417,
  BitVec.ofNat 13 6418,
  BitVec.ofNat 13 6419,
  BitVec.ofNat 13 6424,
  BitVec.ofNat 13 6425,
  BitVec.ofNat 13 6528,
  BitVec.ofNat 13 6529,
  BitVec.ofNat 13 6536,
  BitVec.ofNat 13 6537,
  BitVec.ofNat 13 6544,
  BitVec.ofNat 13 6545,
  BitVec.ofNat 13 6552,
  BitVec.ofNat 13 6553
]

@[simp] theorem p13AscendingCodes12_size : p13AscendingCodes12.size = 15 := by
  decide

/-- The exact 399-code ascending schedule used by the packed curvature rows. -/
def p13AscendingCodes : Array P13LabelCode :=
  p13AscendingCodes00 ++
    p13AscendingCodes01 ++
    p13AscendingCodes02 ++
    p13AscendingCodes03 ++
    p13AscendingCodes04 ++
    p13AscendingCodes05 ++
    p13AscendingCodes06 ++
    p13AscendingCodes07 ++
    p13AscendingCodes08 ++
    p13AscendingCodes09 ++
    p13AscendingCodes10 ++
    p13AscendingCodes11 ++
    p13AscendingCodes12

@[simp] theorem p13AscendingCodes_size : p13AscendingCodes.size = 399 := by
  simp [p13AscendingCodes,
    p13AscendingCodes00_size,
    p13AscendingCodes01_size,
    p13AscendingCodes02_size,
    p13AscendingCodes03_size,
    p13AscendingCodes04_size,
    p13AscendingCodes05_size,
    p13AscendingCodes06_size,
    p13AscendingCodes07_size,
    p13AscendingCodes08_size,
    p13AscendingCodes09_size,
    p13AscendingCodes10_size,
    p13AscendingCodes11_size,
    p13AscendingCodes12_size]

/-- Fixed-width directory for constant-depth lookup in the proof-selected
`399`-code carrier.  Reading one code selects one of thirteen small chunks;
it never unfolds the full appended array. -/
def p13AscendingCodeTable :
    StructuralExhaustion.Core.ChunkedArrayLookup.Table P13LabelCode where
  width := 32
  chunks := #[
    p13AscendingCodes00, p13AscendingCodes01, p13AscendingCodes02,
    p13AscendingCodes03, p13AscendingCodes04, p13AscendingCodes05,
    p13AscendingCodes06, p13AscendingCodes07, p13AscendingCodes08,
    p13AscendingCodes09, p13AscendingCodes10, p13AscendingCodes11,
    p13AscendingCodes12]
  fallback := 0#13

/-- Constant-depth lookup in the proof-selected 399-code carrier. -/
def p13AscendingCode (index : Fin 399) : P13LabelCode :=
  p13AscendingCodeTable.getD index.1

/-- For each of the thirteen path positions, the targets containing that
position, packed in ascending-carrier order. -/
def p13AscendingFeatureColumns : Array (BitVec 399) := #[
  BitVec.ofNat 399 860749930495974554564144787445531520178949539162726328384986876228874532254315047438950028077262639337228357305406499397,
  BitVec.ofNat 399 960424128141183181525530466809304306256559173194784051372851733996494630547758699413100847455884699894639643306167318,
  BitVec.ofNat 399 43299492462981742404833208656896428569561223273391284927872598618090527478685577064016467525361581347245562527896,
  BitVec.ofNat 399 1032707873144614414065749566981566484748503655265138738510612051500980736837224858031191883167744029958371783851999506656,
  BitVec.ofNat 399 1215395438673334389883857085185840519323873261250438463714221878210804449090745701819251962509056042919459950747429388032,
  BitVec.ofNat 399 36553193581716705748294918233884225430093994795795509028055416959366750488506975750789073732107455598411776,
  BitVec.ofNat 399 54333197512534028470567661760556905522877885066663793386985951149920457064448,
  BitVec.ofNat 399 1286082712360555636436061171820112746340877191690379855595771838731692047350735813349526636840111764705002414538559062016,
  BitVec.ofNat 399 1291123707730797352918404391877994519106460710530560876173513879551868186011448050996727681590796901548219693399434854400,
  BitVec.ofNat 399 36695977855307147426792906804234635626202651798041821897102698217836867177670348515811591356578649740410880,
  BitVec.ofNat 399 57896042893221511014144593536140640416404123690391852508421237491862796763136,
  BitVec.ofNat 399 1291124939043417598850103744857320164030528120919603630033600697557788623445292274156973895358823367987905742334385455104,
  BitVec.ofNat 399 1291124939043454294827959586001505937164852838518567137757231966484831306664466670679830343819786895989159582029808926720
]

@[simp] theorem p13AscendingFeatureColumns_size :
    p13AscendingFeatureColumns.size = 13 := by
  decide

/-- One certified carrier-feature column. -/
def p13AscendingFeatureColumn (feature : Fin 13) : BitVec 399 :=
  p13AscendingFeatureColumns.getD feature.1 0#399

end Erdos64EG.Internal
