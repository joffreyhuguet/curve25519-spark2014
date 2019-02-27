with Big_Integers; use Big_Integers;

package Types with
  SPARK_Mode
is

   Min_Add : constant Long_Long_Integer := -2**30 + 1 with Ghost;
   Max_Add : constant Long_Long_Integer := 2**30 - 1 with Ghost;
   Min_Multiply : constant Long_Long_Integer := - (2**27 - 1) with Ghost;
   Max_Multiply : constant Long_Long_Integer := 2**27 - 1 with Ghost;

   type Extended_Index_Type is new Integer range - 1 .. 18;
   subtype Index_Type_Mult is Extended_Index_Type range 0 .. 18;
   subtype Index_Type is Extended_Index_Type range 0 .. 9;

   type Ints is array (Index_Type_Mult range <>) of Long_Long_Integer;
   subtype Ints_Mult is Ints (0 .. 18);
   subtype Ints_256 is Ints (0 .. 9) with
     Dynamic_Predicate => (for all J of Ints_256 => J in -2**31 .. 2**31 - 1);

   type Big_Ints is array (Index_Type_Mult) of Big_Integer with Ghost;
   function Two_Power (Expon : Natural) return Big_Integer is
     (To_Big_Integer (Integer (2)) ** Expon) with Ghost;
   Conversion_Array : constant Big_Ints := (Two_Power (0),   Two_Power (26),
                                            Two_Power (51),  Two_Power (77),
                                            Two_Power (102), Two_Power (128),
                                            Two_Power (153), Two_Power (179),
                                            Two_Power (204), Two_Power (230),
                                            Two_Power (255), Two_Power (281),
                                            Two_Power (306), Two_Power (332),
                                            Two_Power (357), Two_Power (383),
                                            Two_Power (408), Two_Power (434),
                                            Two_Power (459)) with Ghost;
end Types;
