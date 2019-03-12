with Big_Integers; use Big_Integers;
with Types; use Types;
with Conversion; use Conversion;

package Curve25519 with
  SPARK_Mode
is

   function Add (X, Y : Integer_256) return Integer_256 with
     Pre  => All_In_Range (X, Y, Min_Add, Max_Add),
     Post => To_Big_Integer (Add'Result) =
               To_Big_Integer (X) + To_Big_Integer (Y);

   function Multiply_1 (X, Y : Integer_256) return Product_Integer with
     SPARK_Mode => Off,
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => To_Big_Integer (Multiply_1'Result) =
               To_Big_Integer (X) * To_Big_Integer (Y);

   function Multiply_2 (X, Y : Integer_256) return Product_Integer with
     SPARK_Mode => Off,
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => To_Big_Integer (Multiply_2'Result) =
               To_Big_Integer (X) * To_Big_Integer (Y);
end Curve25519;
