with Partial_Product_Impl_3; use Partial_Product_Impl_3;

package body Curve25519_Mult with
  SPARK_Mode
is

   function Multiply (X, Y : Ints_256) return Ints_Mult is

      Product : Ints_Mult := (others => 0);
      Aux : Long_Long_Integer;

      --  All content of arrays are in range

      function All_In_Range return Boolean is
         (All_In_Range (X, Y, Min_Multiply, Max_Multiply))
      with Ghost;

      -- Renaming Partial_Product functions

      function Partial_Product (J, K : Index_Type) return Long_Long_Integer is
        (Partial_Product (X, Y, J, K))
      with
        Ghost,
        Pre  => All_In_Range,
        Post =>
          Partial_Product'Result in
          (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
        ..
          2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2;

      procedure Partial_Product_Def (J, K : Index_Type) with
        Ghost,
        Pre  => All_In_Range,
        Post => (if K = Index_Type'Min (9, J + K)
                 then Partial_Product (J, K)
                    = (if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1)
                      * X (J) * Y (K)
                 else Partial_Product (J, K)
                    = Partial_Product (J - 1, K + 1)
                    + X (J) * Y (K)
                      * (if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1));
      procedure Partial_Product_Def (J, K : Index_Type) is null;

      function Partial_Product (J : Index_Type_Mult) return Long_Long_Integer is
        (Partial_Product (X, Y, J))
      with
        Ghost,
        Pre => All_In_Range,
        Post =>
          Partial_Product'Result in
          (-20) * (2**27 - 1)**2
        ..
          20 * (2**27 - 1)**2;

      function Diff_J (J, K : Index_Type) return Big_Integer is
         (Diff_J (X, Y, J, K))
      with
        Ghost;

      procedure Diff_J_Def (J, K : Index_Type) with
        Ghost,
        Post => Diff_J (J, K)
              = (if K = 0
                 then To_Big_Integer (X (J) * Y (K)) * Conversion_Array (J + K)
                 else Diff_J (J, K - 1)
               + To_Big_Integer (Integer (if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1))
                 * To_Big_Integer (X (J) * Y (K))
                 * Conversion_Array (J + K));
      procedure Diff_J_Def (J, K : Index_Type) is
      begin
        pragma Assert (Diff_J_Rec (X, Y, J, K)
                     = (if K = 0
                        then To_Big_Integer (X (J) * Y (K))
                             * Conversion_Array (J + K)
                        else Diff_J_Rec (X, Y, J, K - 1)
                           + To_Big_Integer (Integer (if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1))
                             * To_Big_Integer (X (J) * Y (K))
                             * Conversion_Array (J + K)));
      end Diff_J_Def;
      --  First J+9 indexes of Product at step J

      function Step_J (J : Index_Type) return Ints with
        Ghost,
        Pre  => All_In_Range,
        Post =>
            Step_J'Result'First = 0
            and then Step_J'Result'Last = J + 9
            and then (for all K in 0 .. J =>
                        Step_J'Result (K) = Partial_Product (K))
            and then (for all K in J + 1 .. J + 9 =>
                        Step_J'Result (K) = Partial_Product (J, K - J));

      function Step_J (J : Index_Type) return Ints is
         Result : Ints (0 .. J + 9) := (others => 0);
      begin
         for K in 0 .. J loop
            Result (K) := Partial_Product (K);
            pragma Loop_Invariant (for all L in 0 .. K =>
                                     Result (L) = Partial_Product (L));
         end loop;
         for K in J + 1 .. J + 9 loop
            Result (K) := Partial_Product (J, K - J);
            pragma Loop_Invariant (for all L in J + 1 .. K =>
                                     Result (L) = Partial_Product (J, L - J));
         end loop;
         return Result;
      end Step_J;

      --  This function returns the array that should be in output

      function Final_Array return Ints_Mult is
         (Step_J (9))
      with
        Ghost,
        Pre  => All_In_Range,
        Post => (for all J in Index_Type_Mult range 0 .. 18 =>
                   Final_Array'Result (J) = Partial_Product (J));



      --  Proves postcondition after the loop

      procedure Prove_Multiply with
        Ghost,
        Pre   =>
          All_In_Range
          and then Product = Step_J (9),
        Post  => To_Integer_Mult (Product) = To_Integer_256 (X) * To_Integer_256 (Y);
      procedure Prove_Multiply is
         X_256, Product_BI : Big_Integer := Zero;
         Old_X, Old_Product : Big_Integer;

         --  This lemma proves that two arrays with the same beginning have a partial conversion equal

         function Add_Next (Product : Big_Integer; J, K : Index_Type) return BIg_Integer
         is
         (Product + To_Big_Integer (X (J))
                            * To_Big_Integer (Y (K))
                            * To_Big_Integer (Integer ((if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1)))
                            * Conversion_Array (J + K))
         with
           Pre  => All_In_Range,
           Post => Add_Next'Result = Product + To_Big_Integer (X (J))
                                               * To_Big_Integer (Y (K))
                                               * To_Big_Integer (Integer ((if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1)))
                                               * Conversion_Array (J + K);

         procedure Prove_LI (J, K : Index_Type) with
           Pre  =>
             Old_Product = Old_X * To_Integer_256 (Y)
                         + To_Big_Integer (X (J)) * (if K = 0 then Zero else Conversion_Array (J)
                           * Partial_Conversion (Y, K - 1))
             and then Product_BI = Old_Product + To_Big_Integer (X (J))
                                                 * To_Big_Integer (Y (K))
                                                 * To_Big_Integer (Integer ((if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1)))
                                                 * Conversion_Array (J + K),
           Post => Product_BI = Old_X * To_Integer_256 (Y)
                              + To_Big_Integer (X (J)) * Conversion_Array (J)
                                * Partial_Conversion (Y, K);
         procedure Prove_LI (J, K : Index_Type) is
         begin
            Conversion_Array_Lemma (J, K);
            if (J + K) mod 2 = 0 and then K mod 2 = 1 then
               pragma Assert (Two_Power (1) = To_Big_Integer (Integer (2)));
               pragma Assert (Product_BI = Old_Product + To_Big_Integer (X (J)) * Conversion_Array (J + K) * To_Big_Integer (Y (K)) * Two_Power (1));
               pragma Assert (Two_Power (1) * Conversion_Array (J + K) = Conversion_Array (J) * Conversion_Array (K));
               pragma Assert (Two_Power (1) * Conversion_Array (J + K) * To_Big_Integer (X (J)) * To_Big_Integer (Y (K))
                              = Conversion_Array (J) * Conversion_Array (K) * To_Big_Integer (X (J)) * To_Big_Integer (Y (K)));
               pragma Assert (PRoduct_BI = Old_Product + Conversion_Array (J) * Conversion_Array (K) * To_Big_Integer (X (J)) * To_Big_Integer (Y (K)));
            else
               pragma Assert (Conversion_Array (J + K) = Conversion_Array (J) * Conversion_Array (K));
               pragma Assert (Conversion_Array (J + K) * To_Big_Integer (X (J)) * To_Big_Integer (Y (K))
                              = Conversion_Array (J) * Conversion_Array (K) * To_Big_Integer (X (J)) * To_Big_Integer (Y (K)));
               pragma Assert (Product_BI = Old_Product + To_Big_Integer (X (J)) * Conversion_Array (J) * To_Big_Integer (Y (K)) * Conversion_Array (K));
            end if;

            if K > 0 then
               pragma Assert (Partial_Conversion (Y, K - 1) + To_Big_Integer (Y (K)) * Conversion_Array (K) = Partial_COnversion (Y, K));
               pragma Assert (Product_BI = Old_X * To_Integer_256 (Y)
                              + To_Big_Integer (X (J)) * Conversion_Array (J)
                                * Partial_Conversion (Y, K));
            else
               pragma Assert (Partial_Conversion (Y, 0) = To_Big_Integer (Y (0)) * Conversion_Array (0));
                              pragma Assert (Product_BI = Old_X * To_Integer_256 (Y)
                              + To_Big_Integer (X (J)) * Conversion_Array (J)
                                * Partial_Conversion (Y, K));
            end if;
         end PRove_LI;

         procedure Equal_Conversion (A, B : Ints; L : Index_Type_Mult) with
           Pre =>
             A'Length > 0
             and then A'First = 0
             and then B'First = 0
             and then B'Last <= A'Last
             and then L in B'Range
             and then (for all J in 0 .. L => A (J) = B (J)),
           Post => Partial_Conversion (A, L) = Partial_Conversion (B, L);
         procedure Equal_Conversion (A, B : Ints; L : Index_Type_Mult) is
         begin

            if L = 0 then
               pragma Assert (Partial_Conversion_Rec (A, L)
                              = To_Big_Integer (A (0)) * Conversion_Array (0));
               pragma Assert (Partial_Conversion_Rec (B, L)
                              = To_Big_Integer (B (0)) * Conversion_Array (0));
               return;
            end if;

            pragma Assert (Partial_Conversion_Rec (A, L)
                           = Partial_Conversion_Rec (A, L - 1)
                           + To_Big_Integer (A (L)) * Conversion_Array (L));
            Equal_Conversion (A, B, L - 1);
            pragma Assert (Partial_Conversion (A, L) = Partial_Conversion (B, L));
         end Equal_Conversion;

         --  This lemma proves a relation between Step_J (J - 1) and Step_J (J)

         procedure First_Step with
           Ghost,
           Pre  =>
             All_In_Range
             and then Product_BI = Diff_J (0, 9),
           Post => Product_BI = Partial_Conversion (Step_J (0), 9);
         procedure First_Step is
           Conversion, Previous : Big_Integer := Zero;
            begin
            for K in Index_Type range 0 .. 9 loop
               Previous := Conversion;
               Conversion := Conversion
                           + To_Big_Integer (X (0) * Y (K))
                             * Conversion_Array (K);
               Diff_J_Def (0, K);

               if K > 0 then
                  pragma Assert (Diff_J (0, K)
                               = Diff_J (0, K - 1)
                               + To_Big_Integer (X (0) * Y (K))
                                 * Conversion_Array (K));
                  pragma Assert (Partial_Conversion (Step_J (0), K)
                               = Partial_Conversion (Step_J (0), K - 1)
                               + To_BIg_Integer (Step_J (0) (K)) * Conversion_Array (K));
                  Partial_Product_Def (0, K);
                  pragma Assert (Step_J (0) (K) = Partial_Product (0, K));
                  pragma Assert (Partial_Product (0, K) = X (0) * Y (K));
               else
                  pragma Assert (Diff_J (0, 0) = To_Big_Integer (X (0) * Y (0))
                                                 * Conversion_Array (0));
                end if;

               pragma Loop_Invariant (Conversion = Diff_J (0, K));
               pragma Loop_Invariant (Conversion = Partial_Conversion (Step_J (0), K));
            end loop;
         end First_Step;

         procedure Step_Up (J : Index_Type) with
           Ghost,
           Pre =>
             All_In_Range
             and then J > 0
             and then Product_BI
                    = Partial_Conversion (Step_J (J - 1), J + 8) + Diff_J (J, 9),
           Post => Product_BI = Partial_Conversion (Step_J (J), J + 9);

         procedure Step_Up (J : Index_Type) is
         Conversion, Previous : Big_Integer := Partial_Conversion (Step_J (J), J - 1);

         procedure Prove_First_LI (K : Index_Type) with
           Pre  =>
             All_In_Range
             and then J > 0
             and then Previous = Partial_Conversion (Step_J (J), J + K - 1)
             and then Conversion
                    = Previous
                    + To_Big_Integer (Step_J (J) (J + K)) * Conversion_Array (J + K),
           Post => Conversion = Partial_Conversion (Step_J (J), J + K);
         procedure Prove_First_LI (K : Index_Type) is
         begin
           Partial_Product_Def (J, K);
           pragma Assert (Conversion
                        = Partial_Conversion (Step_J (J), J + K - 1)
                        + To_Big_Integer (Step_J (J) (J + K)) * Conversion_Array (J + K));
         end Prove_First_LI;

         procedure Prove_Second_LI (K : Index_Type) with
           Pre  =>
             All_In_Range
             and then J > 0
             and then K < 9
             and then Previous = Partial_Conversion (Step_J (J - 1), J + K - 1)
                               + (if K = 0 then Zero else Diff_J (J, K - 1))
             and then Conversion
                    = Previous
                    + To_Big_Integer (Step_J (J) (J + K)) * Conversion_Array (J + K),
           Post => Conversion = Partial_Conversion (Step_J (J - 1), J + K) + Diff_J (J, K);
         procedure Prove_Second_LI (K : Index_Type) is
         begin
           pragma Assert (Partial_Product (J) = Partial_Product (J, 0));
           pragma Assert (Step_J (J) (J + K) = Partial_Product (J, K));
           Partial_Product_Def (J, K);
           pragma Assert (Partial_Product (J, K)
                        = Partial_Product (J - 1, K + 1)
                        + (if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K));
           pragma Assert (Step_J (J - 1) (J + K) = Partial_Product (J - 1, K + 1));
           pragma Assert (Step_J (J) (J + K)
                        = Step_J (J - 1) (J + K)
                        + (if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1) * X (J) * Y (K));
           Diff_J_Def (J, K);
           if K > 0 then
              pragma Assert (Diff_J (J, K)
                           = Diff_J (J, K - 1)
                           + To_Big_Integer (Integer ((if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1)))
                             * To_Big_Integer (X (J) * Y (K))
                             * Conversion_Array (J + K));
              pragma Assert (To_Big_Integer (Step_J (J) (J + K)) * Conversion_Array (J + K)
                           = To_Big_Integer (Step_J (J - 1) (J + K)) * Conversion_Array (J + K)
                           + To_Big_Integer (Integer ((if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1)))
                             * To_Big_Integer (X (J) * Y (K))
                             * Conversion_Array (J + K));
           else
              pragma Assert (Diff_J (J, 0)
                           = To_Big_Integer (X (J) * Y (0)) * Conversion_Array (J));
              pragma Assert (To_Big_Integer (Step_J (J) (J + K)) * Conversion_Array (J + K)
                           = To_Big_Integer (Step_J (J - 1) (J + K)) * Conversion_Array (J + K)
                           + To_Big_Integer (X (J) * Y (0))
                             * Conversion_Array (J));
           end if;

         end Prove_Second_LI;
         begin
            Equal_Conversion (Step_J (J), Step_J (J - 1), J - 1);
            pragma Assert (Partial_Conversion (Step_J (J), J - 1)
                           = Partial_Conversion (Step_J (J - 1), J - 1));
            for K in Index_Type range 0 .. 9 loop
               Previous := Conversion;
               Conversion := Conversion + To_Big_Integer (Step_J (J) (J + K)) * Conversion_Array (J + K);
               Prove_First_LI (K);
               if K < 9 then
                  Prove_Second_LI (K);
               else
                  Partial_Product_Def (J, 9);
                  Diff_J_Def (J, 9);
                  pragma Assert (Previous = Partial_Conversion (Step_J (J - 1), J + 8) + Diff_J (J, 8));
                  pragma Assert (Step_J (J) (J + 9) = Partial_Product (J, 9));
                  pragma Assert (Partial_Product (J, 9) = (if (J + K) mod 2 = 0 and then 9 mod 2 = 1 then 2 else 1) * X (J) * Y (9));
                  pragma Assert (Diff_J (J, 9)
                               = Diff_J (J, 8)
                               + To_Big_Integer (Integer ((if (J + K) mod 2 = 0 and then 9 mod 2 = 1 then 2 else 1)))
                                 * To_Big_Integer (X (J) * Y (9))
                                 * Conversion_Array (J + 9));
              end if;
               pragma Loop_Invariant (Conversion = Partial_Conversion (Step_J (J), J + K));
               pragma Loop_Invariant (if K < 9 then Conversion = Partial_Conversion (Step_J (J - 1), J + K)
                                                  + Diff_J (J, K));
               pragma Loop_Invariant (if K = 9 then Conversion = Partial_Conversion (Step_J (J - 1), J + 8)
                                                               + Diff_J (J, 9));
            end loop;

         end Step_Up;

      begin
         for J in Index_Type range 0 .. 9 loop
            Old_X := X_256;
            X_256 := X_256 + To_Big_Integer (X (J)) * Conversion_Array (J);
            for K in Index_Type range 0 .. 9 loop
               Old_Product := Product_BI;
               pragma Assert (if K = 0 then
                                 Old_Product = Old_X * To_Integer_256 (Y)
                                else Old_Product = Old_X * To_Integer_256 (Y)
                                                 + To_Big_Integer (X (J)) * Conversion_Array (J)
                                                   * Partial_Conversion (Y, K - 1));
               Product_BI := Add_Next (Product_BI, J, K);

               Prove_LI (J, K);

               Diff_J_Def (J, K);
               pragma Assert (Old_Product = PRoduct_BI'Loop_Entry + (if K > 0 then Diff_J (J, K - 1) else Zero));
               pragma Loop_Invariant (Product_BI = Product_BI'Loop_Entry + Diff_J (J, K));
               pragma Loop_Invariant (Product_BI
                                    = Old_X * To_Integer_256 (Y)
                                    + To_Big_Integer (X (J)) * Conversion_Array (J)
                                      * Partial_Conversion (Y, K));
            end loop;

            pragma Assert (Product_BI
                         = Old_X * To_Integer_256 (Y)
                         + To_Big_Integer (X (J)) * Conversion_Array (J)
                           * Partial_Conversion (Y, 9));
            pragma Assert (Partial_Conversion (Y, 9) = To_Integer_256 (Y));
            pragma Assert (Product_BI
                        = (Old_X + To_Big_Integer (X (J))
                          * Conversion_Array (J)) * To_Integer_256 (Y));

            if J = 0 then
               First_Step;
            else
               Step_Up (J);
            end if;

            pragma Loop_Invariant (Product_BI = Partial_Conversion (Step_J (J), J + 9));
            pragma Loop_Invariant (X_256 = Partial_Conversion (X, J));
            pragma Loop_Invariant (Product_BI = X_256 * To_Integer_256 (Y));
         end loop;

         pragma Assert (Product_BI = Partial_Conversion (Step_J (9), 18));
         Equal_Conversion (Product, Step_J (9), 18);
         pragma Assert (Partial_Conversion (Step_J (9), 18) = Partial_Conversion (Product, 18));
         pragma Assert (Product_BI = Partial_Conversion (Product, 18));
         pragma Assert (Partial_Conversion (Product, 18) = To_Integer_Mult (Product));
         pragma Assert (Product_BI = To_Integer_Mult (Product));
         pragma Assert (Product_BI = Partial_Conversion (X, 9) * To_Integer_256 (Y));
         pragma Assert (Partial_Conversion (X, 9) = To_Integer_256 (X));
         pragma Assert (To_Integer_Mult (Product) = To_Integer_256 (X) * To_Integer_256 (Y));
      end Prove_Multiply;
   begin

      for J in Extended_Index_Type range 0 .. 9 loop
         for K in Extended_Index_Type range 0 .. 9 loop
            pragma Assert (X (J) in Min_Multiply .. Max_Multiply
                             and then Y (K) in Min_Multiply .. Max_Multiply);
            pragma Assert (X (J) * Y (K) in - (2**27 - 1)**2 .. (2**27 - 1)**2);
            Aux := X (J) * Y (K) * (if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1);
            pragma Assert (Aux = X (J) * Y (K) * (if (J + K) mod 2 = 0 and then K mod 2 = 1 then 2 else 1));
            pragma Assert (Aux in (-2) * (2**27 - 1)**2 .. 2 * (2**27 - 1)**2);
            Product (J + K) := Product (J + K) + Aux;

            Partial_Product_Def (J, K);

            if K /= Index_Type'Min (9, J + K) then
               pragma Assert (Product (J + K) = Partial_Product (J - 1, K + 1) + Aux);
               pragma Assert (Product (J + K) = Partial_Product (J, K));
            else
              pragma Assert (Product (J + K) = Aux);
              pragma Assert (Product (J + K) = Partial_Product (J, K));
            end if;



            pragma Assert (Product (J + K) in
                             (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
                           ..
                             2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2);

            pragma Loop_Invariant ((for all L in 0 .. J - 1 =>
                                      Product (L) = Product'Loop_Entry (L))
                                   and then
                                     (for all L in J + K + 1 .. 18 =>
                                        Product (L) = Product'Loop_Entry (L)));

            pragma Loop_Invariant (for all L in J .. J + K =>
                                     Product (L) in
                                     (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
                                   ..
                                     2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2);

            pragma Loop_Invariant (for all L in J .. J + K =>
                                     Product (L) = Partial_Product (J, L - J));

         end loop;

         pragma Assert (for all K in 0 .. J - 1 => Product (K) = Step_J (J) (K));
         pragma Assert (Partial_Product (J, 0) = Partial_Product (J));

         pragma Loop_Invariant (for all L in J + 10 .. 18 =>
                                  Product (L) = Product'Loop_Entry (L));

         pragma Loop_Invariant (for all L in Extended_Index_Type range 0 .. 18 =>
                                  Product (L) in
                                  (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
                                ..
                                  2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2);

         pragma Loop_Invariant (for all K in 0 .. J + 9 =>
                                  Product (K) = Step_J (J) (K));

      end loop;

      pragma Assert (for all K in Index_Type_Mult range 0 .. 18 =>
                       Product (K) = Step_J (9) (K));
      pragma Assert (Product = Final_Array);

      Prove_Multiply;

      return Product;
   end Multiply;
end Curve25519_Mult;
