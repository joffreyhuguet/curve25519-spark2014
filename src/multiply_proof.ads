with Types; use Types;
with Big_Integers; use Big_Integers;
with Conversion; use Conversion;

package Multiply_Proof with
  SPARK_Mode,
  Ghost
is
   pragma Annotate (GNATprove, Terminating, Multiply_Proof);

   function Partial_Product_Rec (X, Y : Integer_256; J, K : Index_Type) return Long_Long_Integer is
     (if K = Index_Type'Min (9, J + K)
      then (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K)
      else Partial_Product_Rec (X, Y, J - 1, K + 1) + (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K))
       with
         Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => Partial_Product_Rec'Result in
       (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
     ..
       2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2;

   function Partial_Product (X, Y : Integer_256; J, K : Index_Type) return Long_Long_Integer is
     (Partial_Product_Rec (X, Y, J, K))
       with
         Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => Partial_Product'Result in
       (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
     ..
       2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2;

   function Partial_Product (X, Y : Integer_256; J : Product_Index_Type) return Long_Long_Integer is
     (Partial_Product_Rec (X, Y, Index_Type'Min (J, 9), Index_Type'Max (0, J - 9)))
     with
       Pre => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     POst =>
       Partial_Product'Result in
         (-20) * (2**27 - 1)**2
     ..
       20 * (2**27 - 1)**2;

   procedure Partial_Product_Def (X, Y : Integer_256; J, K : Index_Type) with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => (if K = Index_Type'Min (9, J + K)
                  then Partial_Product (X, Y, J, K)
              = (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1)
              * X (J) * Y (K)
                  else Partial_Product (X, Y, J, K)
              = Partial_Product (X, Y, J - 1, K + 1)
              + X (J) * Y (K)
              * (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1));
   procedure Partial_Product_Def (X, Y : Integer_256; J, K : Index_Type) is null;

   function Partial_Product_Next (X, Y : Integer_256; J, K : Index_Type) return Long_Long_Integer is
     ((if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K))
       with
         Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     POst =>
       Partial_Product_Next'Result in
         (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
     ..
       2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2;

   function Diff_J_Rec (X, Y : Integer_256; J, K : Index_Type) return Big_Integer is
     (if K = 0
      then (+X (J) * Y (K)) * Conversion_Array (J + K)
      else Diff_J_Rec (X, Y, J, K - 1)
      + (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
      * (+X (J) * Y (K))
      * Conversion_Array (J + K));

   function Diff_J (X, Y : Integer_256; J, K : Index_Type) return Big_Integer is
     (Diff_J_Rec (X, Y, J, K));

   procedure Diff_J_Def (X, Y : Integer_256; J, K : Index_Type) with
     Post => Diff_J (X, Y, J, K)
     = (if K = 0
          then (+X (J) * Y (K)) * Conversion_Array (J + K)
          else Diff_J (X, Y, J, K - 1)
        + (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
        * (+X (J) * Y (K))
        * Conversion_Array (J + K));
   procedure Diff_J_Def (X, Y : Integer_256; J, K : Index_Type) is null;

   function Add_Next_BI (Product : Big_Integer; X, Y : Integer_256; J, K : Index_Type) return BIg_Integer
   is
     (Product + (+X (J))
      * (+Y (K))
      * (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
      * Conversion_Array (J + K))
       with
         Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => Add_Next_BI'Result = Product + (+X (J))
       * (+Y (K))
     * (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
     * Conversion_Array (J + K);

   function Step_J (X, Y : Integer_256; J : Index_Type) return Integer_Curve25519 with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post =>
       Step_J'Result'First = 0
       and then Step_J'Result'Last = J + 9
       and then (for all K in 0 .. J =>
                   Step_J'Result (K) = Partial_Product (X, Y, K))
       and then (for all K in J + 1 .. J + 9 =>
                   Step_J'Result (K) = Partial_Product (X, Y, J, K - J));

   function Final_Array (X, Y : Integer_256) return Product_Integer is
     (Step_J (X, Y, 9))
       with
         Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post => (for all J in Product_Index_Type range 0 .. 18 =>
                Final_Array'Result (J) = Partial_Product (X, Y, J));

   procedure Prove_LI (Old_Product, Old_X, Product_BI : Big_Integer; X, Y : Integer_256; J, K : Index_Type) with
     Pre  =>
       Old_Product = Old_X * To_Integer_256 (Y)
     + (+X (J)) * (if K = 0 then Zero else Conversion_Array (J)
                                 * Partial_Conversion (Y, K - 1))
     and then Product_BI = Old_Product + (+(X (J)))
       * (+Y (K))
     * (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
     * Conversion_Array (J + K),
     Post => Product_BI = Old_X * To_Integer_256 (Y)
     + (+X (J)) * Conversion_Array (J)
     * Partial_Conversion (Y, K);

   procedure First_Step (Product_BI : Big_Integer; X, Y : Integer_256) with
     Pre  =>
       All_In_Range (X, Y, Min_Multiply, Max_Multiply)
     and then Product_BI = Diff_J (X, Y, 0, 9),
     Post => Product_BI = Partial_Conversion (Step_J (X, Y, 0), 9);

   procedure Prove_First_LI (Previous, Conversion : Big_Integer; X, Y : Integer_256; J, K : Index_Type) with
     Pre  =>
       All_In_Range (X, Y, Min_Multiply, Max_Multiply)
     and then J > 0
     and then Previous = Partial_Conversion (Step_J (X, Y, J), J + K - 1)
     and then Conversion
       = Previous
     + (+Step_J (X, Y, J) (J + K)) * Conversion_Array (J + K),
     Post => Conversion = Partial_Conversion (Step_J (X, Y, J), J + K);

   procedure Prove_Second_LI (Previous, Conversion : Big_Integer; X, Y : Integer_256; J, K : Index_Type) with
     Pre  =>
       All_In_Range (X, Y, Min_Multiply, Max_Multiply)
     and then J > 0
     and then K < 9
     and then Previous = Partial_Conversion (Step_J (X, Y, J - 1), J + K - 1)
       + (if K = 0 then Zero else Diff_J (X, Y, J, K - 1))
     and then Conversion
       = Previous
     + (+Step_J (X, Y, J) (J + K)) * Conversion_Array (J + K),
     Post => Conversion = Partial_Conversion (Step_J (X, Y, J - 1), J + K) + Diff_J (X, Y, J, K);

   procedure Step_Up (Product_BI : Big_Integer; X, Y : Integer_256; J : Index_Type) with
     Pre =>
       All_In_Range (X, Y, Min_Multiply, Max_Multiply)
     and then J > 0
     and then Product_BI
       = Partial_Conversion (Step_J (X, Y, J - 1), J + 8) + Diff_J (X, Y, J, 9),
     Post => Product_BI = Partial_Conversion (Step_J (X, Y, J), J + 9);

   procedure Prove_Multiply (X, Y : Integer_256; Product : Product_Integer) with
     Pre   =>
       All_In_Range (X, Y, Min_Multiply, Max_Multiply)
     and then Product = Step_J (X, Y, 9),
     Post  => To_Integer_Mult (Product) = To_Integer_256 (X) * To_Integer_256 (Y);
end Multiply_Proof;
