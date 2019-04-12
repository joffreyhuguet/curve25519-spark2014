with Multiply_Proof; use Multiply_Proof;

package body Curve25519_Mult with
  SPARK_Mode
is

   --------------
   -- Multiply --
   --------------

   function Multiply (X, Y : Integer_255) return Product_Integer is
      Product : Product_Integer := (others => 0);
   begin
      for J in Index_Type loop
         for K in Index_Type loop
            Product (J + K) :=
              Product (J + K)
              + X (J) * Y (K) * (if J mod 2 = 1 and then K mod 2 = 1 then 2 else 1);

            Partial_Product_Def (X, Y, J, K);
            --  Reminding definition of Partial_Product

            pragma Loop_Invariant ((for all L in 0 .. J - 1 =>
                                      Product (L) = Product'Loop_Entry (L))
                                   and then
                                     (for all L in J + K + 1 .. 18 =>
                                        Product (L) = Product'Loop_Entry (L)));
            --  To signify at which indexes content has not been changed

            pragma Loop_Invariant (for all L in J .. J + K =>
                                     Product (L) = Partial_Product (X, Y, J, L - J));
            --  Increasingly proving the value of Product (L)

         end loop;

         pragma Loop_Invariant (for all L in J + 10 .. 18 =>
                                  Product (L) = Product'Loop_Entry (L));
         --  To signify at which indexes content has not been changed

         pragma Loop_Invariant (for all L in Product_Index_Type =>
                                  Product (L) in
                                  (-2) * Long_Long_Integer (J + 1) * (2**27 - 1)**2
                                ..
                                  2 * Long_Long_Integer (J + 1) * (2**27 - 1)**2);
         --  To prove overflow checks

         pragma Loop_Invariant (for all L in 0 .. J + 9 =>
                                  Product (L) = Array_Step_J (X, Y, J) (L));
         --  Product is partially equal to Array_Step_J (X, Y, J);

      end loop;
      Prove_Multiply (X, Y, Product);
      return Product;
   end Multiply;
end Curve25519_Mult;
