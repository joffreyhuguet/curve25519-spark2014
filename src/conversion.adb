package body Conversion with
  SPARK_Mode
is

   procedure Equal_To_Conversion (A, B : Integer_Curve25519; L : Product_Index_Type) is
   begin

      if L = 0 then
         pragma Assert (Partial_Conversion_Rec (A, L)
                        = (+A (0)) * Conversion_Array (0));
         pragma Assert (Partial_Conversion_Rec (B, L)
                        = (+B (0)) * Conversion_Array (0));
         return;
      end if;

      pragma Assert (Partial_Conversion_Rec (A, L)
                     = Partial_Conversion_Rec (A, L - 1)
                     + (+A (L)) * Conversion_Array (L));
      Equal_To_Conversion (A, B, L - 1);
      pragma Assert (Partial_Conversion (A, L) = Partial_Conversion (B, L));
   end Equal_To_Conversion;
end Conversion;
