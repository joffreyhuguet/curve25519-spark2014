with Big_Integers; use Big_Integers;
with Types; use Types;
with Conversion; use Conversion;

package Curve25519_Add with
  SPARK_Mode
is

   function Add (X, Y : Integer_256) return Integer_256 with
     Pre  => All_In_Range (X, Y, Min_Add, Max_Add),
     Post => To_Big_Integer (Add'Result) =
               To_Big_Integer (X) + To_Big_Integer (Y);

end Curve25519_Add;
