package body Conversion with
  SPARK_Mode
is

   -------------------------
   -- Equal_To_Conversion --
   -------------------------

   --  This lemma is proved with a manual induction.

   procedure Equal_To_Conversion
     (A, B : Integer_Curve25519;
      L    : Product_Index_Type)
   is
   begin

      if L = 0 then
         return;                         --  Initialization of lemma
      end if;

      Equal_To_Conversion (A, B, L - 1); --  Calling lemma for L - 1
   end Equal_To_Conversion;
end Conversion;
