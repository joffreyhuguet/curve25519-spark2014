with Big_Integers; use Big_Integers;

package Types with
  SPARK_Mode
is

   --  Index types used in implementations

   type Extended_Index_Type is range - 1 .. 18;
   subtype Product_Index_Type is Extended_Index_Type range 0 .. 18;
   subtype Index_Type is Extended_Index_Type range 0 .. 9;

   --  Array types used in implementations

   type Integer_Curve25519 is array (Product_Index_Type range <>) of Long_Long_Integer
     with Dynamic_Predicate => Integer_Curve25519'First = 0;
   subtype Product_Integer is Integer_Curve25519 (0 .. 18);
   --  Integer_256 are arrays of 32 bits integers
   subtype Integer_256 is Integer_Curve25519 (0 .. 9) with
     Dynamic_Predicate => (for all J of Integer_256 => J in -2**31 .. 2**31 - 1);
   type Conversion_Array_Type is array (Product_Index_Type) of Big_Integer with Ghost;

   --  Constants and predicates used in implementations

   Min_Add : constant Long_Long_Integer := -2**30 + 1 with Ghost;
   Max_Add : constant Long_Long_Integer := 2**30 - 1 with Ghost;
   Min_Multiply : constant Long_Long_Integer := - (2**27 - 1) with Ghost;
   Max_Multiply : constant Long_Long_Integer := 2**27 - 1 with Ghost;
   function All_In_Range
     (X, Y     : Integer_256;
      Min, Max : Long_Long_Integer)
      return     Boolean
   is
     (for all J in X'Range =>
         X (J) in Min .. Max
         and then Y (J) in Min .. Max);
end Types;
