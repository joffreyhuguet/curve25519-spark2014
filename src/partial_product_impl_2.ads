with Types; use Types;

package Partial_Product_Impl_2 with
  SPARK_Mode,
  Ghost
is
   pragma Annotate (GNATprove, Terminating, Partial_Product_Impl_2);

   Min_Multiply : constant Long_Long_Integer := - (2**27 - 1) with Ghost;
   Max_Multiply : constant Long_Long_Integer := 2**27 - 1 with Ghost;

   function Partial_Product_Rec (X, Y : Ints_256; J, K : Index_Type_Mult) return Long_Long_Integer is
     (if K = Extended_Index_Type'Max(J - 9, 0) then (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K)
      else Partial_Product_Rec (X, Y, J, K - 1) + (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K))
   with
     Ghost,
     Pre  =>
       J in Index_Type_Mult'Range
       and then K in Index_Type'Range
       and then J - K in Index_Type'Range
       and then (for all J in X'Range =>
                X (J) in Min_Multiply .. Max_Multiply
                and then Y (J) in Min_Multiply .. Max_Multiply),
     Post => Partial_Product_Rec'Result in (-2) * Long_Long_Integer (K + 1) * (2**27 - 1)**2 .. 2 * Long_Long_Integer (K + 1) * (2**27 - 1)**2;

   function Partial_Product (X, Y : Ints_256; J, K : Index_Type_Mult) return Long_Long_Integer is
     (Partial_Product_Rec (X, Y, J, K))
   with
     Ghost,
     Pre  =>
       J in Index_Type_Mult'Range
       and then K in Index_Type'Range
       and then J - K in Index_Type'Range
       and then (for all J in X'Range =>
                   X (J) in Min_Multiply .. Max_Multiply
                   and then Y (J) in Min_Multiply .. Max_Multiply),
     Post => Partial_Product'Result in (-2) * Long_Long_Integer (K + 1) * (2**27 - 1)**2 .. 2 * Long_Long_Integer (K + 1) * (2**27 - 1)**2;

   function Partial_Product (X, Y : Ints_256; J : Index_Type_Mult) return Long_Long_Integer is
      (Partial_Product_Rec (X, Y, J, Extended_Index_Type'Min (9, J)))
   with
     Ghost,
     Pre  =>
       J in Index_Type_Mult'Range
       and then (for all J in X'Range =>
                   X (J) in Min_Multiply .. Max_Multiply
                   and then Y (J) in Min_Multiply .. Max_Multiply);
end Partial_Product_Impl_2;
