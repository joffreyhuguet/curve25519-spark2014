with Big_Integers; use Big_Integers;
with Types; use Types;
with Conversion; use Conversion;

package Curve25519_Mult with
  SPARK_Mode
is
   function Multiply (X, Y : Ints_256) return Ints_Mult with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => To_Integer_Mult (Multiply'Result)
           = To_Integer_256 (X) * To_Integer_256 (Y);
end Curve25519_Mult;
