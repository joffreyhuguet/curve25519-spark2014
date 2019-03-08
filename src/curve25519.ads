with Big_Integers; use Big_Integers;
with Types; use Types;
with Conversion; use Conversion;

package Curve25519 with
  SPARK_Mode
is

   function Add (X, Y : Integer_256) return Integer_256 with
     Pre  => All_In_Range (X, Y, Min_Add, Max_Add),
     Post => To_Integer_256 (Add'Result) =
               To_Integer_256 (X) + To_Integer_256 (Y);

   function Multiply_1 (X, Y : Integer_256) return Product_Integer with
     SPARK_Mode => Off,
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => To_Integer_Mult (Multiply_1'Result) =
               To_Integer_256 (X) * To_Integer_256 (Y);

   function Multiply_2 (X, Y : Integer_256) return Product_Integer with
     SPARK_Mode => Off,
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => To_Integer_Mult (Multiply_2'Result) =
               To_Integer_256 (X) * To_Integer_256 (Y);
end Curve25519;
