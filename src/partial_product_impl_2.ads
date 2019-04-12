with Types; use Types;

package Partial_Product_Impl_2 with
  SPARK_Mode,
  Ghost
is
   function Partial_Product_Rec
     (X, Y : Integer_255;
      J    : Product_Index_Type;
      K    : Index_Type)
      return Long_Long_Integer
   is
     (if K = Extended_Index_Type'Max(J - 9, 0)
      then
        (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K)
      else
         Partial_Product_Rec (X, Y, J, K - 1)
      + (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K))
   with
     Pre  =>
       J - K in Index_Type'Range
       and then All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => Partial_Product_Rec'Result in
             (-2) * Long_Long_Integer (K + 1) * (2**27 - 1)**2
             ..
             2 * Long_Long_Integer (K + 1) * (2**27 - 1)**2;
   pragma Annotate (GNATprove, Terminating, Partial_Product_Rec);

   function Partial_Product
     (X, Y : Integer_255;
      J    : Product_Index_Type;
      K    : Index_Type)
      return Long_Long_Integer
   is
     (Partial_Product_Rec (X, Y, J, K))
   with
     Pre  =>
       J - K in Index_Type'Range
       and then All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => Partial_Product'Result in
             (-2) * Long_Long_Integer (K + 1) * (2**27 - 1)**2
             ..
             2 * Long_Long_Integer (K + 1) * (2**27 - 1)**2;

   procedure Partial_Product_Def
     (X, Y : Integer_255;
      J    : Product_Index_Type;
      K    : Index_Type)
   with
     Pre  =>
       J - K in Index_Type'Range
       and then All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => (if K = Extended_Index_Type'Max(J - 9, 0)
              then
                Partial_Product_Rec (X, Y, J, K)
              = (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K)
              else
                Partial_Product_Rec (X, Y, J, K)
              = Partial_Product_Rec (X, Y, J, K - 1)
              + (if J mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (K) * Y (J - K));
   procedure Partial_Product_Def
     (X, Y : Integer_255;
      J    : Product_Index_Type;
      K    : Index_Type)
   is null;

   function Partial_Product
     (X, Y : Integer_255;
      J    : Product_Index_Type)
      return Long_Long_Integer
   is
      (Partial_Product_Rec (X, Y, J, Extended_Index_Type'Min (9, J)))
   with
     Pre => All_In_Range (X, Y, Min_Multiply, Max_Multiply);
end Partial_Product_Impl_2;
