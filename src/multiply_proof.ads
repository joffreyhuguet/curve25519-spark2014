with Big_Integers; use Big_Integers;
with Conversion;   use Conversion;
with Types;        use Types;

package Multiply_Proof with
  SPARK_Mode,
  Ghost
is
   pragma Annotate (GNATprove, Terminating, Multiply_Proof);

   -------------------------------
   -- Partial_Product functions --
   -------------------------------

   --  These functions will be used to follow the value of Product
   --  within the loop.

   function Partial_Product_Rec
     (X, Y : Integer_256;
      J, K : Index_Type)
      return Long_Long_Integer
   is
     (if K = Index_Type'Min (9, J + K)
      then (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K)
      else Partial_Product_Rec (X, Y, J - 1, K + 1)
           + (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K))
   with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post =>
       Partial_Product_Rec'Result in
       (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
     ..
       2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2;
   --  Function used to represent Product (J + K) within the loop.
   --  Product (J + K) = Partial_Product_Rec (X, Y, J, K) is a loop
   --  invariant.

   function Partial_Product
     (X, Y : Integer_256;
      J, K : Index_Type)
      return Long_Long_Integer
   is
     (Partial_Product_Rec (X, Y, J, K))
   with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post =>
       Partial_Product'Result in
       (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
     ..
       2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2;
   --  Wrapper for recursive function Partial_Product_Rec

   function Partial_Product
     (X, Y : Integer_256;
      L    : Product_Index_Type)
      return Long_Long_Integer
   is
     (Partial_Product_Rec
       (X, Y, Index_Type'Min (L, 9), Index_Type'Max (0, L - 9)))
     with
     Pre => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post =>
       Partial_Product'Result in
       (-20) * (2**27 - 1)**2
     ..
       20 * (2**27 - 1)**2;
   --  Value of Product (L) at the end of the two loops

   procedure Partial_Product_Def
     (X, Y : Integer_256;
      J, K : Index_Type)
   with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post =>
       (if K = Index_Type'Min (9, J + K)
        then Partial_Product (X, Y, J, K)
             = (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1)
               * X (J) * Y (K)
        else Partial_Product (X, Y, J, K)
             = Partial_Product (X, Y, J - 1, K + 1)
               + X (J) * Y (K)
                 * (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1));
   procedure Partial_Product_Def
     (X, Y : Integer_256;
      J, K : Index_Type)
   is null;
   --  This procedure is sometimes needed to remind the expression of
   --  Partial_Product to solvers.

   -----------------------------------------------
   -- Array_Step_J functions and related lemmas --
   -----------------------------------------------

   function Array_Step_J
     (X, Y : Integer_256;
      J    : Index_Type)
      return Integer_Curve25519
   with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post =>
       Array_Step_J'Result'First = 0
       and then Array_Step_J'Result'Last = J + 9
       and then (for all K in 0 .. J =>
                   Array_Step_J'Result (K) = Partial_Product (X, Y, K))
       and then (for all K in J + 1 .. J + 9 =>
                   Array_Step_J'Result (K) = Partial_Product (X, Y, J, K - J));
   --  Array_Step_J is equal to Product at the end of loop J

   function Final_Array (X, Y : Integer_256) return Product_Integer is
     (Array_Step_J (X, Y, 9))
   with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post =>
       (for all J in Product_Index_Type =>
          Final_Array'Result (J) = Partial_Product (X, Y, J));
   --  Final_Array is equal to the output of Multiply

   -------------------------------------
   -- Diff_Step_J and other functions --
   -------------------------------------

   function Diff_Step_J
     (X, Y : Integer_256;
      J, K : Index_Type)
      return Big_Integer
   is
     (if K = 0
      then (+X (J) * Y (K)) * Conversion_Array (J + K)
      else Diff_Step_J (X, Y, J, K - 1)
           + (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
             * (+X (J) * Y (K))
             * Conversion_Array (J + K));
   --  Diff_Step_J_Rec is equal to
   --  Partial_Conversion (Array_Step_J (X, Y, J), J + K)
   --  - Partial_Conversion (Array_Step_J (X, Y, J - 1), J + K),
   --  i.e it is equal to the big integer added to Product in loop J

   procedure Diff_Step_J_Def (X, Y : Integer_256; J, K : Index_Type) with
     Post =>
       Diff_Step_J (X, Y, J, K)
       = (if K = 0
          then (+X (J) * Y (K)) * Conversion_Array (J + K)
          else Diff_Step_J (X, Y, J, K - 1)
               + (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
                 * (+X (J) * Y (K))
                 * Conversion_Array (J + K));
   procedure Diff_Step_J_Def (X, Y : Integer_256; J, K : Index_Type) is null;
   --  This procedure is sometimes needed to remind the expression of
   --  Diff_Step_J to solvers.

   function Add_Factor
     (Product : Big_Integer;
      X, Y    : Integer_256;
      J, K    : Index_Type)
      return    Big_Integer
   is
     (Product + (+X (J))
     * (+Y (K))
     * (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
     * Conversion_Array (J + K))
   with
     Pre  => All_In_Range (X, Y, Min_Multiply, Max_Multiply),
     Post =>
       Add_Factor'Result
       = Product + (+X (J))
         * (+Y (K))
         * (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
         * Conversion_Array (J + K);
   --  Add_Factor adds the J-K factor to a big integer

   procedure Array_Step_J_To_Next
     (Product_Conversion : Big_Integer;
      X, Y               : Integer_256;
      J                  : Index_Type)
   with
     Pre =>
       All_In_Range (X, Y, Min_Multiply, Max_Multiply)
       and then
         Product_Conversion
         = (if J = 0 then Zero else Partial_Conversion (Array_Step_J (X, Y, J - 1), J + 8))
           + Diff_Step_J (X, Y, J, 9),
     Post => Product_Conversion = Partial_Conversion (Array_Step_J (X, Y, J), J + 9);
   --  Array_Step_J_To_Next is the definition of Diff_Step_J, that allows to
   --  obtain Partial_Conversion (Array_Step_J (X, Y, J), J + 9) from
   --  Partial_Conversion (Array_Step_J (X, Y, J - 1), J + 8) and
   --  Diff_Step_J (X, Y, J, 9).

   procedure Array_Diff_Lemma
     (Previous, Conversion : Big_Integer;
      X, Y                 : Integer_256;
      J, K                 : Index_Type)
   with
     Pre            =>
       All_In_Range (X, Y, Min_Multiply, Max_Multiply)
       and then J > 0
       and then
         Previous
         = Partial_Conversion (Array_Step_J (X, Y, J - 1), J + K - 1)
           + (if K = 0 then Zero else Diff_Step_J (X, Y, J, K - 1))
       and then
         Conversion
         = Previous
           + (+Array_Step_J (X, Y, J) (J + K)) * Conversion_Array (J + K),
     Contract_Cases =>
       (K < 9 =>
          Conversion
        = Partial_Conversion (Array_Step_J (X, Y, J - 1), J + K)
        + Diff_Step_J (X, Y, J, K),
        K = 9 =>
          Conversion
        = Partial_Conversion (Array_Step_J (X, Y, J - 1), J + 8)
        + Diff_Step_J (X, Y, J, 9));
   --  Array_Diff_Lemma establishes a link between Array_Step_J (X, Y, J - 1)
   --  and Array_Step_J (X, Y, J) via Partial_Conversion and Diff_Step_J.

   ----------------------
   -- Other procedures --
   ----------------------

   procedure Split_Product
     (Old_Product, Old_X, Product_Conversion : Big_Integer;
      X, Y                                   : Integer_256;
      J, K                                   : Index_Type)
   with
     Pre  =>
       Old_Product
       = Old_X * (+Y)
         + (+X (J))
           * (if K = 0
              then Zero
              else Conversion_Array (J) * Partial_Conversion (Y, K - 1))
     and then
       Product_Conversion
       = Old_Product
         + (+X (J)) * (+Y (K))
           * (+(if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1))
           * Conversion_Array (J + K),
     Post =>
       Product_Conversion
       = Old_X * (+Y)
         + (+X (J)) * Conversion_Array (J)
           * Partial_Conversion (Y, K);
   --  This function splits the conversion of factor J-K into conversion
   --  of factor J and K in X and Y respectively.

   procedure Prove_Multiply
     (X, Y    : Integer_256;
      Product : Product_Integer)
   with
     Pre  =>
       All_In_Range (X, Y, Min_Multiply, Max_Multiply)
       and then Product = Array_Step_J (X, Y, 9),
     Post => (+Product) = (+X) * (+Y);
   --  Proves the property of Multiply for Final_Array
end Multiply_Proof;
