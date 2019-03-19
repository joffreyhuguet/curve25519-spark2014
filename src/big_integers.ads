package Big_Integers with
  Ghost,
  SPARK_Mode
is
   pragma Annotate (GNATprove, External_Axiomatization);

   type Big_Integer is private;
   Zero : constant Big_Integer;

   function "="  (L, R : Big_Integer) return Boolean with Import;
   function "<"  (L, R : Big_Integer) return Boolean with Import;
   function "<=" (L, R : Big_Integer) return Boolean with Import;
   function ">"  (L, R : Big_Integer) return Boolean with Import;
   function ">=" (L, R : Big_Integer) return Boolean with Import;

   function To_Big_Integer (Arg : Integer)           return Big_Integer with
     Import;
   function To_Big_Integer (Arg : Long_Long_Integer) return Big_Integer with
     Import;
   function "+" (Arg : Long_Long_Integer) return Big_Integer
     renames To_Big_Integer;

   function In_Range (Arg, Low, High : Big_Integer) return Boolean is
     ((Low <= Arg) and (Arg <= High))
   with
     Import;

   function To_Integer (Arg : Big_Integer) return Integer with
     Import,
     Pre => In_Range (Arg,
                      Low  => To_Big_Integer (Integer'First),
                      High => To_Big_Integer (Integer'Last));

   function "-" (L : Big_Integer)      return Big_Integer with Import;
   function "abs" (L : Big_Integer)    return Big_Integer with Import;
   function "+" (L, R : Big_Integer)   return Big_Integer with Import;
   function "-" (L, R : Big_Integer)   return Big_Integer with Import;
   function "*" (L, R : Big_Integer)   return Big_Integer with Import;
   function "/" (L, R : Big_Integer)   return Big_Integer with
     Import,
     Pre => R /= Zero;
   function "mod" (L, R : Big_Integer) return Big_Integer with
     Import,
     Pre => R /= Zero;
   function "rem" (L, R : Big_Integer) return Big_Integer with
     Import,
     Pre => R /= Zero;
   function "**" (L : Big_Integer; R : Natural)
     return Big_Integer
   with
     Import;
   function Min (L, R : Big_Integer) return Big_Integer with Import;
   function Max (L, R : Big_Integer) return Big_Integer with Import;

private
   pragma SPARK_Mode (Off);

   type Big_Integer is null record;
   Zero : constant Big_Integer := (null record);
end Big_Integers;
