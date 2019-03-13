with Big_Integers; use Big_Integers;
with Types; use Types;
with Conversion; use Conversion;

package Curve25519_Other_Mult with
  SPARK_Mode
is
   function Multiply_1 (X, Y : Integer_256) return Product_Integer with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => (+Multiply_1'Result) =
               (+X) * (+Y);

   function Multiply_2 (X, Y : Integer_256) return Product_Integer with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => (+Multiply_2'Result) =
               (+X) * (+Y);
end Curve25519_Other_Mult;
