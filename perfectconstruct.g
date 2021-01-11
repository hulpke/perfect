# construct perfect groups of given order
# Usage:
# Practice(order); # practice makes perfect
# Practice(order:from:=[[factorgrouporders],[indexpositions]]); for partial
# MakePerfectGroupOrders(seedorders) extends list of orders by 2, by adding
# simple groups and products with prime powers, excluding coprime primes

Read("tabletrans.g");

# Orders that were not covered in Holt/Plesken lists
#PERFUNKNOWN:=Filtered(SizesPerfectGroups(),x->NrPerfectLibraryGroups(x)=0);
PERFUNKNOWN:=[61440, 86016, 122880, 172032, 245760, 344064, 368640, 491520,
688128, 737280, 983040 ];

#Limit for TransformingPermutationsCharacterTables (class number) in
#identifying factor groups
TPCTLIMIT:=200;

# seed is list of orders
MakePerfectGroupOrders:=function(seed)
local from, upto,it,sim,i,a,ord,pp,j;
  seed:=Filtered(seed,x->x>1);
  from:=Maximum(seed)+1;
  upto:=2*Maximum(seed);
  it:=SimpleGroupsIterator(1,upto);
  sim:=[];
  ord:=[];
  for i in it do
    a:=Size(i);
    Add(sim,a);
    if a>=from and a<=upto then
      Add(ord,a);
    fi;
  od;
  
  # Direct Products of simple
  pp:=ShallowCopy(sim);

  repeat
    a:=Set(ShallowCopy(pp));
    for i in pp do
      for j in sim do
        if i*j<=upto and not i*j in a then
          AddSet(a,i*j);
        fi;
      od;
    od;
    if a<>pp then
      pp:=a;
      a:=false; #to force continue
    fi;
  until a<>false;

  ord:=Union(ord,Filtered(pp,x->x>=from));
  Print("Fitting-Free:",ord,"\n");

  pp:=Filtered([1..QuoInt(upto,Minimum(seed))],IsPrimePowerInt);

  for i in seed do
    a:=QuoInt(upto,i);
    for j in Filtered(pp,x->x<=a) do
      if Gcd(i,j)>1 or not IsPrimeInt(j) then
        AddSet(ord,i*j);
      fi;
    od;
  od;
  ord:=Filtered(ord,x->x>=from and x<=upto);
  return ord;
end;

# functions that could be used as isomorphism distinguishers
GpFingerprint:=function(g)
  if Size(g)<2000 and Size(g)<>512 and Size(g)<>1024 and Size(g)<>1536 then
    return IdGroup(g);
  else
    return [Size(g),IsPerfect(g),Collected(List(ConjugacyClasses(g),
      x->[Order(Representative(x)),Size(x)]))];
  fi;
end;

FPMaxReps:=function(g,a,b)
local l,s;
  l:=LowLayerSubgroups(g,a);
  s:=Set(List(l,Size));
  RemoveSet(s,Size(g));
  s:=Reversed(s);
  if b>Length(s) then return [];fi;
  return Filtered(l,x->Size(x)=s[b]);
end;

FINGERPRINTPROPERTIES:=[
  g->Collected(List(ConjugacyClasses(g),x->[Order(Representative(x)),Size(x)])),
  g->Collected(List(ConjugacyClasses(g),x->[Order(Representative(x)),GpFingerprint(Centralizer(x))])),
  g->Collected(List(MaximalSubgroupClassReps(g),GpFingerprint)),
  g->Collected(List(NormalSubgroups(g),x->[GpFingerprint(x),GpFingerprint(Centralizer(g,x))])),
  g->Collected(List(LowLayerSubgroups(g,2),GpFingerprint)),

  g->Size(AutomorphismGroup(g)),
  g->Collected(List(CharacteristicSubgroups(g),x->[GpFingerprint(x),GpFingerprint(Centralizer(g,x))])),
  #g->Collected(Flat(Irr(CharacterTable(g)))),
];

CHEAPFINGERPRINTLIMIT:=4;  # the first 4 fingerprint tests are cheap-ish

GrplistIds:=function(l)
local props,pool,test,c,f,r,tablecache,tmp,cheaplim;
  test:=function(p)
  local a,new,sel,i,dup,tmp;
    if c=Length(l) then return;fi;# not needed
    dup:=List(Filtered(Collected(pool),x->x[2]>1),x->x[1]);
    sel:=Filtered([1..Length(l)],x->pool[x] in dup);
    a:=[];
    for i in sel do
      tmp:=Group(GeneratorsOfGroup(l[i]));
      SetSize(tmp,Size(l[i]));
      a[i]:=p(tmp);
    od;
    if ForAny(dup,x->Length(Set(a{Filtered(sel,y->pool[y]=x)}))>1) then
      for i in sel do Add(pool[i],a[i]); od;
      Add(props,p);
      c:=Length(Set(pool));
    fi;
  end;

  props:=[];
  pool:=List(l,x->[]);c:=1;
  for f in FINGERPRINTPROPERTIES do test(f);od;
  cheaplim:=PositionProperty(List(props,x->Position(FINGERPRINTPROPERTIES,x)),
    x->x>CHEAPFINGERPRINTLIMIT);
  if cheaplim=fail then cheaplim:=Length(props);
  else cheaplim:=cheaplim-1;fi;

  if c<Length(l) then
    tablecache:=[];
    Print("will have to rely on isomorphism tests\n");
  fi;

  r:=rec(props:=props,pool:=pool,
    groupinfo:=List(l,x->[Size(x),GeneratorsOfGroup(x)]),
    isomneed:=Filtered([1..Length(pool)],x->Number(pool,y->y=pool[x])>1),

    idfunc:=function(arg)
      local gorig,a,f,p,g,fingerprints,cands,badset,goodset,i,cheap,rprop;
        gorig:=arg[1];
        if Length(arg)>1 then
          badset:=arg[2];
          goodset:=arg[3];
        else
          badset:=[];
          goodset:=[];
        fi;
        cheap:=arg[Length(arg)]=true; #do cheap test only?

        if Length(r.pool)=1 then return 1;fi;
        g:=gorig;

        if IsBound(g!.fingerprints) then
          fingerprints:=g!.fingerprints;
        else
          fingerprints:=[];
          g!.fingerprints:=fingerprints;
        fi;
        if IsPermGroup(g) then
          if IsSolvableGroup(g) then
            g:=Image(IsomorphismPcGroup(g));
          else
            g:=Image(SmallerDegreePermutationRepresentation(g));
          fi;
          a:=Size(g);
          g:=Group(GeneratorsOfGroup(g)); # avoid caching lots of data
          SetSize(g,a);
        fi;
        a:=[];
        if cheap then rprop:=r.props{[1..cheaplim]};
        else rprop:=r.props;fi;
        for f in rprop do
          p:=PositionProperty(fingerprints,x->x[1]=f);
          if p=fail then
            Add(a,f(g));
            Add(fingerprints,[f,a[Length(a)]]);
          else
            Add(a,fingerprints[p][2]);
          fi;
          cands:=Filtered([1..Length(r.pool)],x->
            Length(r.pool[x])>=Length(a) and r.pool[x]{[1..Length(a)]}=a);
          if IsSubset(badset,cands) then 
            Print("badcand ",cands,"\n");
            return "bad";
          fi;
          if IsSubset(goodset,cands) then
            Print("goodcand ",cands,"\n");
            return "good";
          fi;
          if Length(cands)>1 then Print("Cands=",cands,"\n");fi;

          p:=Position(r.pool,a);
          if IsInt(p) and not p in r.isomneed then return p;fi;
        od;
        if cheap then
          a:=Filtered([1..Length(r.pool)],
            x->r.pool[x]{[1..Minimum(cheaplim,Length(r.pool[x]))]}=a);
          return a;
        fi;

        a:=Filtered([1..Length(r.pool)],x->r.pool[x]=a);

	if Length(ConjugacyClasses(g))<=TPCTLIMIT then
	  f:=Length(a);
	  for i in ShallowCopy(a) do
	    if Length(a)>1 then
	      if not IsBound(tablecache[i]) then
		tmp:=Group(r.groupinfo[i][2]);
		SetSize(tmp,r.groupinfo[i][1]);
		tmp:=ShallowCopy(CharacterTable(tmp));
                Size(tmp);
                Irr(tmp);
                Unbind(tmp!.ConjugacyClasses); # avoid caching groups
                Unbind(tmp!.UnderlyingGroup);
		tablecache[i]:=tmp;
	      fi;
	      if TransformingPermutationsCharacterTablesTimeout(
                 CharacterTable(g),tablecache[i],
                 QuoInt(Size(g),5000))=fail then
		RemoveSet(a,i);
	      fi;
	    fi;
	  od;
	  if Length(a)<f then
	    Print("Character table test reduces ",f,"->", Length(a),"\n");
	  fi;
	fi;

	while Length(a)>1 do
	  i:=a[1];
	  a:=a{[2..Length(a)]};
          tmp:=Group(r.groupinfo[i][2]);
          SetSize(tmp,r.groupinfo[i][1]);
	  if IsomorphismGroups(g,tmp)<>fail then
	    return i;
	  fi;
	od;
	return a[1];
      end);
  l:=false; # clean memory
  return r;
end;

#IdGrplist:=function(r,g)
#  return r.idfunc(g);
#end;

if not IsBound(PERFECTLIST) then
  PERFECTLIST:=[];
fi;

MemoryEfficientVersion:=function(G)
local piso,f,k,pf,new;
  piso:=IsomorphismPermGroup(G);
  f:=FreeGroup(List(GeneratorsOfGroup(FreeGroupOfFpGroup(G)),String));
  new:=f/List(RelatorsOfFpGroup(G),x->MappedWord(x,FreeGeneratorsOfFpGroup(G),
    GeneratorsOfGroup(f)));
  k:=List(SMALLGENERATINGSETGENERIC(Image(piso)),
    x->PreImagesRepresentative(piso,x));
  pf:=List(k,x->ImagesRepresentative(piso,x));
  k:=List(k,x->ElementOfFpGroup(FamilyObj(One(new)),MappedWord(
    UnderlyingElement(x),FreeGeneratorsOfFpGroup(G),GeneratorsOfGroup(f))));
  #pf:=MappingGeneratorsImages(piso)[2];
  pf:=GroupHomomorphismByImagesNC(new,Group(pf),k,pf);
  SetIsomorphismPermGroup(new,pf);
  return new;
end;

MyIsomTest:=function(g,h)
local c,d,f;
  for f in FINGERPRINTPROPERTIES do
    if f(g)<>f(h) then return false;fi;
  od;
  if Length(ConjugacyClasses(g))<500 then
    c:=CharacterTable(g);;Irr(c);
    d:=CharacterTable(h);;Irr(d);
    if TransformingPermutationsCharacterTablesTimeout(c,d,
      QuoInt(Size(g),5000))=fail then return false; fi;
  fi;

  c:=Size(g);
  if Length(GeneratorsOfGroup(g))>5 then 
    g:=Group(SmallGeneratingSet(g));
    SetSize(g,c);
  fi;
  if Length(GeneratorsOfGroup(h))>5 then 
    h:=Group(SmallGeneratingSet(h));
    SetSize(h,c);
  fi;
  return IsomorphismGroups(g,h)<>fail;
end;

# split out as that might help with memory
DoPerfectConstructionFor:=function(q,j,nts,ids)
local respp,cf,m,mpos,coh,fgens,comp,reps,v,new,isok,pema,pf,gens,nt,quot,
      res,qk,p,e,k,primax;

  primax:=NrPerfectGroups(Size(q));
  p:=Factors(nts)[1];
  e:=LogInt(nts,p);
  res:=[];
  respp:=[];

  # is there a chance for modules -- which factors would fit into GL
  quot:=Size(GL(e,p));
  cf:=Filtered(NormalSubgroups(q),x->IndexNC(q,x)>1 
    and (quot mod IndexNC(q,x)=0));
  if Length(cf)=0 then cf:=q;
  else cf:=Intersection(cf);fi;
  
  if Size(cf)=1 then
    new:=IdentityMapping(q);
    cf:=IrreducibleModules(q,GF(p),e);
    if cf[1]<>GeneratorsOfGroup(q) then Error("gens1");fi;
  elif Size(cf)=Size(q) then
    Print("Dimension is too small for nontrivial factors\n");
    cf:=[GeneratorsOfGroup(q),[TrivialModule(Length(GeneratorsOfGroup(q)),GF(p))]];
  else
    new:=NaturalHomomorphismByNormalSubgroup(q,cf);
    Print("Reduced module question to factor of order ",Size(Range(new)),"\n");
    fgens:=List(GeneratorsOfGroup(q),x->ImagesRepresentative(new,x));
    cf:=IrreducibleModules(GroupWithGenerators(fgens),GF(p),e);
    if cf[1]<>fgens then Error("gens2");fi;
    cf:=[GeneratorsOfGroup(q),cf[2]];
  fi;

  cf:=Filtered(cf[2],x->x.dimension=e);

  for m in cf do
    mpos:=Position(cf,m);
    Print("Module dimension ",m.dimension,"\n");
    coh:=TwoCohomologyGeneric(q,m);
    fgens:=GeneratorsOfGroup(coh.presentation.group);

    comp:=[];
    if Length(coh.cohomology)=0 then
      reps:=[coh.zero];
    elif Length(coh.cohomology)=1 and p=2 then
      reps:=[coh.zero,coh.cohomology[1]];
    else
      comp:=CompatiblePairs(q,m);
      reps:=CompatiblePairOrbitRepsGeneric(comp,coh);
    fi;
    Print("Compatible pairs ",Size(comp)," give ",Length(reps),
          " orbits from ",Length(coh.cohomology),"\n");
    for v in reps do
      new:=FpGroupCocycle(coh,v,true);
      isok:=IsPerfect(new);

      if isok then
        # could it have been gotten in another way?
        pema:=IsomorphismPermGroup(new);
        pema:=pema*SmallerDegreePermutationRepresentation(Image(pema));
        pf:=Image(pema);

        # generators that give module action
        gens:=List(coh.presentation.prewords,
          x->MappedWord(x,fgens,GeneratorsOfGroup(pf){[1..Length(fgens)]}));
        # want: generated through smallest normal subgroup, first
        # module of this kind for factor, first factor group
        #nt:=Filtered(NormalSubgroups(pf),IsElementaryAbelian);
        nt:=Filtered(MinimalNormalSubgroups(pf),x->IsPrimePowerInt(Size(x)));
        if ForAll(nt,x->Size(x)>=nts) then
          nt:=Filtered(nt,x->Size(x)=nts);

          # leave out the one how it was created
          quot:=GroupHomomorphismByImagesNC(pf,coh.group,
            List(GeneratorsOfGroup(new),x->ImagesRepresentative(pema,x)),
              Concatenation(
              List(GeneratorsOfGroup(Range(coh.fphom)),
                x->PreImagesRepresentative(coh.fphom,x)),
                ListWithIdenticalEntries(coh.module.dimension, 
                  One(coh.group))
                ));
          qk:=KernelOfMultiplicativeGeneralMapping(quot);
          nt:=Filtered(nt,x->x<>qk);

          # consider the factor groups:
          # any smaller index -> discard
          # any equal index -> test
          # otherwise accept

          # first do all with cheap test only (to find bad)
          k:=1;
          while isok<>false and k<=Length(nt) do
            qk:=ids.idfunc(pf/nt[k],[1..j-1],[j+1..primax],
              true); # cheap test
            if (IsInt(qk) and qk<j) or qk="bad" then isok:=false;fi;
            k:=k+1;
          od;

          if isok=false then
            Print("quickdiscard\n");
          else
            k:=1;
            while isok<>false and k<=Length(nt) do
              qk:=ids.idfunc(pf/nt[k],[1..j-1],[j+1..primax]);
              if (IsInt(qk) and qk<j) or qk="bad" then isok:=false;
              elif IsInt(qk) and qk=j then isok:=fail;fi;
              k:=k+1;
            od;
          fi;

          if (isok<>false and ForAll(respp,x->MyIsomTest(x,pf)=false)) then
            Add(res,new);
            Add(respp,pf); # local list
            Print("found nr. ",Length(res),"\n");
          else
            Print("smallerc\n");
          fi;

        else
          Print("smallera\n");
        fi;
      else
        Print("not perfect\n");
      fi;
    od;

  od; #for m

  # cleanup of cached data to save memory
  for m in [1..Length(res)] do
    res[m]:=MemoryEfficientVersion(res[m]);

  od;
  return res;
end;

# option from is list, entry 1 is orders, entry s2, if given, indices
Practice:=function(n) #makes perfect
local globalres,resp,d,i,j,nt,p,e,q,cf,m,coh,v,new,quot,nts,pf,pl,comp,reps,
      ids,all,gens,fgens,mpos,ntm,dosubdir,isok,qk,k,respp,pema,from,ran,
      old;

  if n>=60^6 then Error("Cannot do yet");fi;
  from:=ValueOption("from");
  dosubdir:=false;

  globalres:=[];

  # simple groups
  ran:=SimpleGroupsIterator(n,n);
  for i in ran do Add(globalres,i);od;

  #resp:=[];
  q:=SizesPerfectGroups();
  d:=Filtered(DivisorsInt(n),x->x<n and x in q);

  if from<>fail then d:=Intersection(d,from[1]);fi;

  for i in d do
    nts:=n/i;
    if IsPrimePowerInt(nts) then
      pl:=[];
      if NrPerfectLibraryGroups(i)=0 then
        all:=PERFECTLIST[i];
      else
        all:=List([1..NrPerfectGroups(i)],x->PerfectGroup(IsPermGroup,i,x));
      fi;
      ids:=GrplistIds(all);
      for j in [1..Length(all)] do
        q:=all[j];
        if HasName(q) then
          new:=Name(q);
        else
          new:=Concatenation("Perfect(",String(Size(q)),",",String(j),")");
        fi;
        q:=Group(SmallGeneratingSet(q));
        SetName(q,new);
        Add(pl,q);
      od;

      ran:=[1..Length(pl)];
      if from<>fail and Length(from)>1 and Length(from[1])=1 then
        ran:=from[2];
      fi;
      for j in ran do
        old:=Length(globalres);
        q:=pl[j];
        Print("Using ",i,", ",j,": ",q,"\n");
        Append(globalres,DoPerfectConstructionFor(q,j,nts,ids));
        Print("Total now: ",Length(globalres)," groups\n");
        # kill factor group and associated info, as not needed any longer
        Unbind(pl[j]); 

      od; # for j in ran
    elif nts<=i then
      #nts is not prime power, try to do direct products of simple
      q:=SimpleGroupsIterator(nts,nts);
      old:=[];
      for j in q do Add(old,j);od;
      if Length(old)>0 then
        if NrPerfectLibraryGroups(i)=0 then
          all:=PERFECTLIST[i];
        else
          all:=List([1..NrPerfectGroups(i)],x->PerfectGroup(IsPermGroup,i,x));
        fi;
        all:=Filtered(all,x->Size(RadicalGroup(x))=1 and
          (IsSimple(x) or ForAll(MinimalNormalSubgroups(x),y->Size(y)<=nts))
          );
        if Length(all)>0 then
          for j in Cartesian(old,all) do
            Print("Direct Product:",j,"\n");
            j:=List(j,x->Image(IsomorphismFpGroup(x)));
            Add(globalres,DirectProduct(j[1],j[2]));
          od;
        fi;
      fi;
    fi;
  od;
  return globalres;
end;

# Function to generate library file
PrintPerfectStorageData:=function(file,l)
local i,j,a,p,s,w,idx,sz,g,sim,sg,newf,newrels,new,per,o,rk,smallgenfp,gs;

  smallgenfp:=function(a)
  local sz,imgs,i,c;
    sz:=Size(a);
    imgs:=List(GeneratorsOfGroup(a),x->ImagesRepresentative(per,x));
    for i in [1..Length(imgs)] do
      for c in Combinations(imgs,i) do
        if Size(Group(c))=sz then
          return GeneratorsOfGroup(a){List(c,x->Position(imgs,x))};
        fi;
      od;
    od;
  end;

  sz:=Size(l[1]);

  w:=SizeScreen()[1];
  idx:=Position(PERFRec.sizes,sz);
  a:=ShallowCopy(PERFRec.number);
  a[idx]:=Length(l);

  PrintTo(file,
"#############################################################################\n",
"##\n",
"##  This file is part of GAP, a system for computational discrete algebra.\n",
"##  It contains the perfect groups of order ",sz,"\n",
"##  This data was computed by Alexander Hulpke\n",
"##  It is distributed under the artistic license 2.0\n",
"##  https://opensource.org/licenses/Artistic-2.0\n\n");

  AppendTo(file,"number:=",a,";\n\n","PERFGRP[",idx,"]:=[");

  for i in [1..Length(l)] do
    Print("Doing ",i,"\n");
    if i>1 then AppendTo(file,",\n");fi;

    g:=l[i];
    sim:=IsomorphismSimplifiedFpGroup(g); # kill redundant stuff
    sg:=Range(sim);
    rk:=Length(GeneratorsOfGroup(sg));
    newf:=FreeGroup(List([1..Length(GeneratorsOfGroup(sg))],x->[CHARS_LALPHA[x]]));
    newrels:=List(RelatorsOfFpGroup(sg),
      x->MappedWord(x,FreeGeneratorsOfFpGroup(sg),GeneratorsOfGroup(newf)));
    new:=newf/newrels; SetSize(new,Size(g));

    per:=IsomorphismPermGroup(g);
    # reduce degree until kingdom come
    repeat
      p:=NrMovedPoints(Range(per));
      per:=per*SmallerDegreePermutationRepresentation(Image(per));
    until p=NrMovedPoints(Range(per));
    p:=Image(per);
    per:=GroupHomomorphismByImagesNC(new,p,GeneratorsOfGroup(new),
          List(GeneratorsOfGroup(sg),x->ImagesRepresentative(per,
            PreImagesRepresentative(sim,x))));
    SetIsomorphismPermGroup(new,per);
    o:=Orbits(p,MovedPoints(p));
    s:=List(o,x->PreImage(per,Stabilizer(p,x[1])));
    gs:=List(s,x->ShallowCopy(GeneratorsOfGroup(x))); # trigger gens

    AppendTo(file,"# ",sz,".",i,"\n",
    "[[1,\"",CHARS_LALPHA{[1..rk]},"\",\nfunction(");
    for j in [1..rk] do
      if j>1 then AppendTo(file,",");fi;
      AppendTo(file,CHARS_LALPHA{[j]});
    od;
    AppendTo(file,")\nreturn [",newrels,",\n");
    a:=[];
    for j in gs do
      j:=List(j,UnderlyingElement);
      TCENUM.CosetTableFromGensAndRels(FreeGeneratorsOfFpGroup(new),RelatorsOfFpGroup(new),j);
      Add(a,j);
    od;

    AppendTo(file,a,"];\nend,\n",List(o,Length),"],\n\"PG",sz,".",i,"\",",
    "0," # no hpNumber
    );
    a:=Centre(p);
    if IsSimpleGroup(p/a) then
      a:=-Size(a);
    else
      a:=Size(a);
    fi;
    AppendTo(file,a,",");
    # simple factors
    s:=CompositionSeries(p);
    a:=[];
    for j in [2..Length(s)] do
      if not HasAbelianFactorGroup(s[j-1],s[j]) then
        w:=Filtered([1..Length(PERFRec.sizeNumberSimpleGroup)],
          x->PERFRec.sizeNumberSimpleGroup[x][1]=IndexNC(s[j-1],s[j]));
        if Length(w)>1 then Error("size not unique");fi;
        w:=w[1];
        Add(a,w);
      fi;
    od;
    if Length(a)=1 then a:=a[1];fi;

    AppendTo(file,a,",");
    a:=List(o,Length);
    if Length(a)=1 then a:=a[1];fi;
    AppendTo(file,a,"]");
  od;

  AppendTo(file,"];\n");
end;
