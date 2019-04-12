with Big_Integers; use Big_Integers;
with Types; use Types;
with Conversion; use Conversion;

package Curve25519_Add with
  SPARK_Mode
is
   function Add (X, Y : Integer_255) return Integer_255 with
     Pre  => All_In_Range (X, Y, Min_Add, Max_Add),
     Post => +Add'Result = (+X) + (+Y);
end Curve25519_Add;
