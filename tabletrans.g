# This is an almost verbatim copy of library code for
# `TransformingPermutationsCharacterTables`, however with an added timeout
# condition (give maximal permitted runtime).

MatAutomorphismsFamilyTimeout:=
    function( chainG, K, family, permutations,timeout )
    local famlength,             # number of rows in the family
          nonbase,               # points not in the base of `chainG'
          stabilizes,            # local function to check generators of $G$
          gen,                   # loop over `chainG.generators'
          chainK,                # compatible stabilizer chain of $K$
          allowed,               # new parameter for the backtrack search
          ElementPropertyCoset,  # local function to search in a coset
          FindSubgroupProperty;  # local function to extend the stab. chain

    famlength:= Length( permutations );
        
    # Select an optimal base that allows us to prune the tree efficiently.
    nonbase:= Difference( [ 1 .. Length( family) ],
                          BaseStabChain( chainG ) );
    
    # Call a modified version of `SubgroupProperty'.
    # Besides the parameter `K', we introduce the new parameter `allowed',
    # a list of same length as `permutations';
    # `allowed[<i>]' is the list of all <x> in `permutations' where the
    # constructed permutation can lie in
    # `permutations[<i>] * Stab( family> ) / <x>'.
    # Initially this is `permutations' itself, but `allowed' is updated
    # whenever an image of a base point is chosen.
    
    # Find a subgroup $U$ of $G$ which preserves the property <prop>,
    # i.e., $prop( x )$ implies $prop( x * u )$ for all $x \in G, u \in U$.
    # (Note:  This subgroup is changed in the algorithm, be careful!)
    # Make this subgroup as large as possible with reasonable effort!
    
    # Improvement in our special situation:
    # We may add those generators <gen> of $G$ that stabilize the whole row
    # family, i.e. for which holds
    # `<family>[i] = <family>[ i^ ( x^-1 * gen * x ) ]'.
    
    stabilizes:= function( family, gen, x )
      local i;
      for i in [ 1 .. Length( family ) ] do
        if family[ i^x ] <> family[ ( i^gen )^x ] then
          return false;
        fi;
      od;
      return true;
    end;

    K:= SSortedList( K );
    for gen in chainG.generators do
      if ForAll( permutations, x -> stabilizes( family, gen, x ) ) then
        AddSet( K, gen );
      fi;
    od;

    # Make the bases of the stabilizer chains compatible.
    chainK:= StabChainOp( GroupByGenerators( K, () ),
                          rec( base    := BaseStabChain( chainG ),
                               reduced := false ) );

    # Initialize `allowed'.
    allowed:= ListWithIdenticalEntries( famlength, permutations );
    
    # Search through the whole group $G = G * Id$ for an element with <prop>.

    # Search for an element in a coset $S * s$ of some stabilizer $S$ of $G$.
    # $L$ fixes $S*s$, i.e., $S*s*L = S*s$ and is a subgroup of the wanted
    # subgroup $K$, thus $prop( x )$ implies $prop( x*l )$ for all $l \in L$.

    # `S' is a stabilizer chain for $S$,
    # `L' is a list of generators for $L$.
    ElementPropertyCoset := function( S, s, L, allowed )

      local i, j, points, p, ss, LL, elm, newallowed, union;

      if Runtime()>timeout then return -1;fi;
      # If $S$ is the trivial group check whether $s$ has the property,
      # i.e., also the non-base points are mapped correctly.

      if IsEmpty( S.generators ) then
        for i in [ 1 .. famlength ] do
          for p in nonbase do
            allowed[i]:= Filtered( allowed[i],
                           x -> ( p^s )^x in family[ p^permutations[i] ] );
          od;
          if IsEmpty( allowed[i] ) then
            return fail;
          fi;
        od;
        return s;
      fi;

      # Make `points' a subset of $S.orbit ^ s$ of those points which
      # correspond to cosets that might contain elements satisfying <prop>.
      # Make this set as small as possible with reasonable effort!
      points:= SSortedList( OnTuples( S.orbit, s ) );

      # Improvement in our special situation:
      # For the basepoint `$b$ = S.orbit[1]' we have
      # $b \pi \in orbit \cap \bigcap_{i}
      # \bigcup_{\pi_j \in `allowed[i]'} [ family( b \pi_i ) ] \pi_j^{-1}$

      for i in [ 1 .. famlength ] do
        union:= [];
        for j in allowed[i] do
          UniteSet( union, List( family[ S.orbit[1] ^ permutations[i] ],
                                 x -> x / j ) );
        od;
        IntersectSet( points, union );
      od;

      # run through the points, i.e., through the cosets of the stabilizer.
      while not IsEmpty( points ) do

        # Take a point $p$.
        p:= points[1];

        # Find a coset representative,
        # i.e., $ss \in S$ with $S.orbit[1]^ss = p$.
        ss:= s;
        while S.orbit[1]^ss <> p do
          ss:= LeftQuotient( S.transversal[p/ss], ss );
        od;

        # Find a subgroup $LL$ of $L$ which fixes $S.stabilizer * ss$,
        # i.e., an approximation (subgroup) $LL$ of $Stabilizer( L, p )$.
        # note that $LL$ preserves <prop> since it is a subgroup of $L$.
        # Compute a better aproximation, for example using base change.
        # `LL' is a list of generators of $LL$.
        LL:= Filtered( L, l -> p^l = p );

        # Search the coset $S.stabilizer * ss$ and return if successful.

        # In our special situation, we adjust `allowed': 
        newallowed:= [];
        for i in [ 1 .. famlength ] do
          newallowed[i]:= Filtered( allowed[i], x -> p^x in
                              family[ S.orbit[1]^permutations[i] ] );
        od;

        elm:= ElementPropertyCoset( S.stabilizer, ss, LL, newallowed );
        if elm=-1 or Runtime()>timeout then return -1;fi;
        if elm <> fail then return elm; fi;

        # If there was no element in $S.stab * Rep(p)$ satisfying <prop>
        # there can be none in $S.stab * Rep(p^l) = S.stab * Rep(p) * l$
        # for any $l \in L$ because $L$ preserves the property <prop>.
        # Thus we can remove the entire $L$ orbit of $p$ from the points.
        SubtractSet( points, OrbitPerms( L, p ) );

      od;

      # there is no element with the property <prop> in the coset  $S * s$.
      return fail;
    end;

    # Make $L$ the subgroup with the property of some stabilizer $S$ of $G$.
    # Upon entry $L$ is already a subgroup of this wanted subgroup.

    # `S' and `L' are stabilizer chains.
    FindSubgroupProperty := function( S, L, allowed )

      local i, j, points, p, ss, LL, elm, newallowed, union;

      # If $S$ is the trivial group, then so is $L$ and we are ready.
      if IsEmpty( S.generators ) then return; fi;

      # Improvement in our special situation:
      # Adjust `allowed' (we search in the stabilizer of `S.orbit[1]').

      newallowed:= [];
      for i in [ 1 .. famlength ] do
        newallowed[i]:= Filtered( allowed[i],
                                  x -> S.orbit[1]^x in
                                 family[ S.orbit[1]^permutations[i] ] );
      od;

      # Make $L.stab$ the full subgroup of $S.stab$ satisfying <prop>.
      FindSubgroupProperty( S.stabilizer, L.stabilizer, newallowed );
      if Runtime()>timeout then return -1;fi;

      # Add the generators of `L.stabilizer' to `L.generators',
      # update `orbit' and `transversal':
      for elm in L.stabilizer.generators do
        if not elm in L.generators then
          AddGeneratorsExtendSchreierTree( L, [ elm ] );
        fi;
      od;

      # Make `points' a subset of $S.orbit$ of those points which
      # correspond to cosets that might contain elements satisfying <prop>.
      # Make this set as small as possible with reasonable effort!
      points := SSortedList( S.orbit );

      # Improvement in our special situation:
      # For the basepoint `$b$ = S.orbit[1]', we have
      # $b \pi \in orbit \cap \bigcap_{i}
      # \bigcup_{j \in `allowed[i]'} [ family[ b \pi_i ] ] \pi_j^{-1}$.
      for i in [ 1 .. famlength ] do
        union:= [];
        for j in allowed[i] do
          UniteSet( union, List( family[ S.orbit[1] ^ permutations[i] ],
                                 x -> x / j ) );
        od;
        IntersectSet( points, union );
      od;

      # Suppose that $x \in S.stab * Rep(S.orbit[1]^l)$ satisfies <prop>,
      # since $S.stab*Rep(S.orbit[1]^l)=S.stab*l$ we have $x/l \in S.stab$.
      # Because $l \in L$ it follows that $x/l$ satisfies <prop> also, and
      # since $L.stab$ is the full subgroup of $S.stab$ satisfying <prop>
      # it follows that $x/l \in L.stab$ and so $x \in L.stab * l \<= L$.
      # thus we can remove the entire $L$ orbit of $p$ from the points.
      SubtractSet( points, OrbitPerms( L.generators, S.orbit[1] ) );

      # Run through the points, i.e., through the cosets of the stabilizer.
      while not IsEmpty( points ) do

        # Take a point $p$.
        p:= points[1];

        # Find a coset representative,
        # i.e., $ss  \in  S, S.orbit[1]^ss = p$.
        ss:= S.identity;
        while S.orbit[1]^ss <> p do
          ss:= LeftQuotient( S.transversal[p/ss], ss );
        od;

        # Find a subgroup $LL$ of $L$ which fixes $S.stabilizer * ss$,
        # i.e., an approximation (subgroup) $LL$ of $Stabilizer( L, p )$.
        # Note that $LL$ preserves <prop> since it is a subgroup of $L$.
        # Compute a better aproximation, for example using base change.
        LL:= Filtered( L.generators, l -> p^l = p );

        # Search the coset $S.stabilizer * ss$ and add if successful.

        # Adjust `allowed'.
        newallowed:= [];
        for i in [ 1 .. famlength ] do
          newallowed[i]:= Filtered( allowed[i], x -> p^x in
                                   family[ S.orbit[1]^permutations[i] ] );
        od;

        elm:= ElementPropertyCoset( S.stabilizer, ss, LL, newallowed );
        if elm=-1 or Runtime()>timeout then return -1;fi;
        if elm <> fail then
          AddGeneratorsExtendSchreierTree( L, [ elm ] );
        fi;

        # If there was no element in $S.stab * Rep(p)$ satisfying  <prop>
        # there can be none in  $S.stab * Rep(p^l) = S.stab * Rep(p) * l$
        # for any $l \in L$ because $L$ preserves  the  property  <prop>.
        # Thus we can remove the entire $L$ orbit of $p$ from the points.
        # <<this must be reformulated>>
        SubtractSet( points, OrbitPerms( L.generators, p ) );

      od;

      # There is no element with the property <prop> in the coset $S * s$.
      return;
    end;

    FindSubgroupProperty( chainG, chainK, allowed );
    if Runtime()>timeout then return -1;fi;
    return chainK;
end;

TransformingPermutationsTimeout:=function( mat1, mat2,timeout )
    local i, j, k,        # loop variables
          fam1,
          fam2,
          bijection,
          bij_col,        # current bijection of columns of the matrices
          pos,
          G,
          family,
          fam,
          nonfixedpoints,
          famrep,
          support,
          subgrp,
          trans,
          image,
          preimage,
          row1,
          row2,
          values;

    # Step 0:
    # Handle trivial cases.
    if Length( mat1 ) <> Length( mat2 ) then
      return fail;
    elif IsEmpty( mat1 ) then
      return rec( columns := (),
                  rows    := (),
                  group   := GroupByGenerators( [], () ) );
    fi;
    
    # Step 1:
    # Set up and check the bijection of row families using the fact that
    # sorted rows must be equal.
    # (Note that this is only a bijection of the representatives;
    # we do not need a physical bijection of the rows themselves)
    # Note that `FamiliesOfRows' first sorts families according to
    # the representative, and then sorts this list *stable* (using `Sortex')
    # according to the length of the family, so the bijection must
    # be the identity.
    
#T check invariants first (matrix dimensions!)
    fam1:= FamiliesOfRows( mat1, [] );
    fam2:= FamiliesOfRows( mat2, [] );
    if fam1.famreps <> fam2.famreps then
      Info( InfoMatrix, 2,
            "TransformingPermutations: no bijection of row families" );
      return fail;
    fi;
    
    # Step 2:
    # Initialize a bijection of column families using that row
    # families of length 1 must be in bijection, i.e. the column
    # families are constant on these rows.
    # We will have `bij_col[1][i]' in bijection with `bij_col[2][i]'.
    
    bij_col:= [];
    bij_col[1]:= [ [ 1 .. Length( mat1[1] ) ] ]; # trivial column families
    bij_col[2]:= [ [ 1 .. Length( mat1[1] ) ] ];
    
    for i in [ 1 .. Length( fam1.famreps ) ] do
      if Length( fam1.families[i] ) = 1 then
        row1:= mat1[ fam1.families[i][1] ];
        row2:= mat2[ fam2.families[i][1] ];
        for j in [ 1 .. Length( bij_col[1] ) ] do
          preimage:= bij_col[1][j];
          image:=    bij_col[2][j];
          values:= SSortedList( row1{ preimage } );
          if values <> SSortedList( row2{ image } ) then
            Info( InfoMatrix, 2,
                  "TransformingPermutations: ",
                  "no bijection of column families" );
            return fail;
          fi;
          bij_col[1][j]:= Filtered( preimage, x -> row1[x] = values[1] );
          bij_col[2][j]:= Filtered( image, x -> row2[x] = values[1] );
          if Length( bij_col[1][j] ) <> Length( bij_col[2][j] ) then
            Info( InfoMatrix, 2,
                  "TransformingPermutations: ",
                  "no bijection of column families" );
            return fail;
          fi;
          for k in [ 2 .. Length( values ) ] do
            Add( bij_col[1], Filtered( preimage,
                                       x -> row1[x] = values[k] ) );
            Add( bij_col[2], Filtered( image,
                                       x -> row2[x] = values[k] ) );
            if Length( bij_col[1][ Length( bij_col[1] ) ] )
               <> Length( bij_col[2][ Length( bij_col[2] ) ] ) then
              Info( InfoMatrix, 2,
                    "TransformingPermutations: ",
                    "no bijection of column families" );
              return fail;
            fi;
          od;
        od;
      fi;
    od;
    
    # Step 3:
    # Refine the column families and the bijection using that members
    # of a column family must have the same sorted column in the
    # restriction to every row family. Since the trivial row families
    # are already examined, now only use the nontrivial row families.
    # Except that now the values are sorted lists, the algorithm is
    # the same as in step 2.
    
    for i in [ 1 .. Length( fam1.famreps ) ] do
      if Length( fam1.families[i] ) > 1 then
        row1:= MutableTransposedMat( mat1{ fam1.families[i] } );
        row2:= MutableTransposedMat( mat2{ fam2.families[i] } );
        for j in row1 do Sort( j ); od;
        for j in row2 do Sort( j ); od;
        for j in [ 1 .. Length( bij_col[1] ) ] do
          preimage:= bij_col[1][j];
          image:=    bij_col[2][j];
          values:= SSortedList( row1{ preimage } );
          if values <> SSortedList( row2{ image } ) then
            Info( InfoMatrix, 2,
                  "TransformingPermutations: ",
                  "no bijection of column families" );
            return fail;
          fi;
          bij_col[1][j]:= Filtered( preimage,
                                    x -> row1[x] = values[1] );
          bij_col[2][j]:= Filtered( image,
                                    x -> row2[x] = values[1] );
          if Length( bij_col[1][j] ) <> Length( bij_col[2][j] ) then
            Info( InfoMatrix, 2,
                  "TransformingPermutations: ",
                  "no bijection of column families" );
            return fail;
          fi;
          for k in [ 2 .. Length( values ) ] do
            Add( bij_col[1], Filtered( preimage,
                                       x -> row1[x] = values[k] ) );
            Add( bij_col[2], Filtered( image,
                                       x -> row2[x] = values[k] ) );
            if Length( bij_col[1][ Length( bij_col[1] ) ] )
               <> Length( bij_col[2][ Length( bij_col[2] ) ] ) then
              Info( InfoMatrix, 2,
                    "TransformingPermutations: ",
                    "no bijection of column families" );
              return fail;
            fi;
          od;
        od;
      fi;
    od;
    
    # Choose an arbitrary bijection of columns
    # that respects the bijection of column families.
    
    bijection:= [];
    for i in [ 1 .. Length( bij_col[1] ) ] do
      for j in [ 1 .. Length( bij_col[1][i] ) ] do
        bijection[ bij_col[1][i][j] ]:= bij_col[2][i][j];
      od;
    od;
    nonfixedpoints:= Filtered( bij_col[2], x -> 1 < Length(x) );
    
    # Step 4:
    # Compute a direct prouct of symmetric groups that covers the
    # group of table automorphisms of mat2, using column families
    # given by `bij_col[2]'.
    
    G:= [];
    for i in nonfixedpoints do
      Add( G, ( i[1], i[2] ) );
      if 2 < Length( i ) then
        Add( G, MappingPermListList( i,
                    Concatenation( i{[2..Length(i)]}, [ i[1] ] ) ) );
      fi;
    od;
    G:= StabChain( GroupByGenerators( G, () ) );
    
    # Step 5:
    # Enter the backtrack search for permutation groups.

    Info( InfoMatrix, 2,
          "TransformingPermutations: start of backtrack search" );
    
    bij_col:= PermList( bijection );
    
    # Now loop over the row families;
    # first convert `famreps[i]' to `family';
    # `family[<k>]' is the list of all
    # positions <j> in `famreps[i]' with
    # `famreps[i][<k>] = famreps[i][<j>]'.
    # So each permutation stabilizing `famreps[i]' will have to map
    # <k> to a point in `family[<k>]'.
    # (Note that `famreps[i]' is sorted.)
    
    for i in [ 1 .. Length( fam1.famreps ) ] do
      if Length( fam1.permutations[i] ) > 1 then
        famrep:= fam1.famreps[i];
        support:= Length( famrep );
        family:= [ ];
        j:= 1;
        while j <= support do
          family[j]:= [ j ];
          k:= j+1;
          while k <= support and famrep[k] = famrep[j] do
            Add( family[j], k );
            family[k]:= family[j];
            k:= k+1;
          od;
          j:= k;
        od;
        if Runtime()>timeout then return -1;fi;
        subgrp:= MatAutomorphismsFamilyTimeout( G, [], family,
                                         fam2.permutations[i],timeout );
        if subgrp=-1 or Runtime()>timeout then return -1;fi;
        trans:= TransformingPermutationFamily( G, subgrp.generators,
                               fam1.permutations[i],
                               fam2.permutations[i], bij_col,
                               family );
        if trans = fail then
          return fail;
        fi;
        if Runtime()>timeout then return -1;fi;
        G:= subgrp;
        ReduceStabChain( G );
        bij_col:= bij_col * trans;
      fi;
    od;

    # Return the result.
    return rec( columns := bij_col,
                rows    := Sortex( List( mat1, x -> Permuted( x, bij_col ) ) )
                           / Sortex( ShallowCopy( mat2 ) ),
                group   := GroupStabChain( G ) ); 
    end;


# added timeout in seconds. Return -1 if timeout
TransformingPermutationsCharacterTablesTimeout:=
function( tbl1, tbl2,timeout )
    local primes,        # prime divisors of the order of each table
          irr1, irr2,    # lists of irreducible characters of the tables
          trans,         # result record
          gens,          # generators of the matrix automorphisms of `tbl2'
          nccl,          # no. of conjugacy classes
          powermap1,     # list of power maps of `tbl1'
          powermap2,     # list of power maps of `tbl2'
          admissible,    # group of table automorphisms of `tbl2'
          pi, pi2,       # admissible column transformations
          prop,          # property used in `ElementProperty'
          orders1,       # element orders of `tbl1'
          orders2;       # element orders of `tbl2'

    timeout:=Runtime()+1000*timeout; # time when to stop

    # Shortcuts:
    # - If the group orders differ then return `fail'.
    # - If irreducibles are stored in the two tables and coincide,
    #   and if the power maps are known and equal then return the identity.
    primes:= PrimeDivisors( Size( tbl1 ) );
    if Size( tbl1 ) <> Size( tbl2 ) then
      return fail;
    elif HasIrr( tbl1 ) and HasIrr( tbl2 ) and Irr( tbl1 ) = Irr( tbl2 )
         and ForAll( primes, p -> IsBound( ComputedPowerMaps( tbl1 )[p] ) and
                                  IsBound( ComputedPowerMaps( tbl1 )[p] ) and
                                  ComputedPowerMaps( tbl1 )[p] =
                                  ComputedPowerMaps( tbl2 )[p] ) then
      if HasAutomorphismsOfTable( tbl1 ) then
        return rec( columns:= (),
                    rows:= (),
                    group:= AutomorphismsOfTable( tbl1 ) );
      else
        return rec( columns:= (),
                    rows:= (),
                    group:= AutomorphismsOfTable( tbl2 ) );
      fi;
    fi;

    irr1:= Irr( tbl1 );
    irr2:= Irr( tbl2 );

    trans:= TransformingPermutationsTimeout( irr1, irr2, timeout );

    if trans = fail then
      return fail;
    elif trans=-1 or Runtime()>timeout then
      return -1;
    fi;

    gens:= GeneratorsOfGroup( trans.group );                               
    nccl:= NrConjugacyClasses( tbl2 );
    
    # Compute the subgroup of table automorphisms of `tbl2' if it is not
    # yet stored.
    # Note that we know the group of matrix automorphisms already,
    # so we use the same method as in `TableAutomorphisms'.

    powermap1:= List( primes, p -> PowerMap( tbl1, p ) );
    powermap2:= List( primes, p -> PowerMap( tbl2, p ) );

    if HasAutomorphismsOfTable( tbl2 ) then
      admissible:= AutomorphismsOfTable( tbl2 );
    else

      admissible:= Filtered( gens,
                           perm -> ForAll( powermap2,
                                         x -> ForAll( [ 1 .. nccl ],
                                         y -> x[ y^perm ] = x[y]^perm ) ) );
    
      if Length( admissible ) = Length( gens ) then
        admissible:= trans.group;
      else
        Info( InfoCharacterTable, 2,
              "TransformingPermutationsCharTables: ",
              "not all matrix automorphisms admissible" );
        admissible:= SubgroupProperty( trans.group,
                         perm -> ForAll( powermap2, 
                                   x -> ForAll( [ 1 .. nccl ],
                                          y -> x[y^perm] = x[y]^perm ) ),
                                       GroupByGenerators( admissible, () ) );
      fi;

      # Store the automorphisms.
      SetAutomorphismsOfTable( tbl2, admissible );

    fi;
    
    pi:= trans.columns;

    orders1:= OrdersClassRepresentatives( tbl1 );
    orders2:= OrdersClassRepresentatives( tbl2 );

    if ForAll( [ 1 .. Length( primes ) ],
               x -> ForAll( [ 1 .. nccl ],
                    y -> powermap2[x][ y^pi ] = powermap1[x][y]^pi ) )
       and Permuted( orders1, pi ) = orders2 then

      # `pi' itself respects the mappings.
      trans.group:= admissible;

    else
    
      # Look if there is a coset of `trans.group' over `admissible' that
      # consists of transforming permutations.
      prop:= s -> ForAll( [ 1 .. Length( primes ) ],
                          x -> ForAll( [ 1 .. nccl ], y ->
                powermap2[x][ (y^pi)^s ] = ( powermap1[x][y]^pi )^s ) )
             and Permuted( orders1, pi*s ) = orders2;

      pi2:= ElementProperty( trans.group, prop,
                TrivialSubgroup( trans.group ), admissible );
      if pi2 = fail then
        return fail;
      else
        trans:= rec( columns:= pi * pi2,
                     rows:= Sortex( List( irr1,
                                          x -> Permuted( x, pi * pi2 ) ) )
                            / Sortex( ShallowCopy( irr2 ) ),
                     group:= admissible  );
      fi;

    fi;

    # Return the result.
    return trans;
    end;
