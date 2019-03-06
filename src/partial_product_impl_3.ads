with Types; use Types;
with Big_Integers; use Big_Integers;

package Partial_Product_Impl_3 with
  SPARK_Mode,
  Ghost
is
   pragma Annotate (GNATprove, Terminating, Partial_Product_Impl_3);

   function Partial_Product_Rec (X, Y : Ints_256; J, K : Index_Type) return Long_Long_Integer is
      (if K = Index_Type'Min (9, J + K)
       then (if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K)
       else Partial_Product_Rec (X, Y, J - 1, K + 1) + (if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K))
   with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => Partial_Product_Rec'Result in
             (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
             ..
             2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2;

    function Partial_Product (X, Y : Ints_256; J, K : Index_Type) return Long_Long_Integer is
      (Partial_Product_Rec (X, Y, J, K))
   with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => Partial_Product'Result in
             (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
             ..
             2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2;

   function Partial_Product (X, Y : Ints_256; J : Index_Type_Mult) return Long_Long_Integer is
      (Partial_Product_Rec (X, Y, Index_Type'Min (J, 9), Index_Type'Max (0, J - 9)))
   with
     Pre => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     POst =>
       Partial_Product'Result in
       (-20) * (2**27 - 1)**2
     ..
       20 * (2**27 - 1)**2;

   function Diff_J_Rec (X, Y : Ints_256; J, K : Index_Type) return Big_Integer is
     (if K = 0
      then To_Big_Integer (X (J) * Y (K)) * Conversion_Array (J + K)
      else Diff_J_Rec (X, Y, J, K - 1)
         + To_Big_Integer (Integer (if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1))
           * To_Big_Integer (X (J) * Y (K))
           * Conversion_Array (J + K));

   function Diff_J (X, Y : Ints_256; J, K : Index_Type) return Big_Integer is
     (Diff_J_Rec (X, Y, J, K));
end Partial_Product_Impl_3;
