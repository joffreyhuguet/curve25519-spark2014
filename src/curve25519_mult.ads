with Big_Integers; use Big_Integers;
with Types;        use Types;
with Conversion;   use Conversion;

package Curve25519_Mult with
  SPARK_Mode
is
   function Multiply (X, Y : Integer_256) return Product_Integer with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post =>
       To_Big_Integer (Multiply'Result)
     = To_Big_Integer (X) * To_Big_Integer (Y);
end Curve25519_Mult;
