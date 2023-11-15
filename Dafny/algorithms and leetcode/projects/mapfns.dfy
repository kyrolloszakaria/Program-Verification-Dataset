
const highBV: bv16 := 32767
const lowBV: bv16 := -32768;

function pixel2grid(hl: bv16, de: bv16): (cf: bv16) {
	(((hl + 2*de) >> 7) << 8) | ((2*de-hl) >> 7)
}

method mapPixelToGrid(hl: bv16, de: bv16) returns (hlp: bv16)
	// requires lowBV <= hl <= highBV;
	// requires lowBV <= de <= highBV;
	ensures hlp == pixel2grid(hl, de);
{
	// var x: bv16 := (hl + 2*de) >> 7;
	// var y: bv16 := (2*de-hl) >> 7;
	// return (x << 8) | y;
	var a: bv8 := 0;
	var b: bv8 := 0;
	var c: bv8 := 0;

	var stack := new bv16[10];
	stack[0] := hl;
	stack[1] := de;

	var h: bv8 := (hl >> 8) as bv8;
	var l: bv8 := (hl & 0x00FF) as bv8;

	var d: bv8 := (de >> 8) as bv8;
	var e: bv8 := (de & 0x00FF) as bv8;
}