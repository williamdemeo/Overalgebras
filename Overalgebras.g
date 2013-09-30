# File: Overalgebras.g
# Author: William DeMeo
# Date: 2011.05.24
# Updated: 2012.09.24
#
# Description: GAP routines for constructing overalgebras of a given G-set and 
#              for creating uacalc files containing the resulting algebras.
#
# Examples: Many examples are given in the function OveralgebraExample defined below.
#
# Please send questions, comments, and suggestions to williamdemeo@gmail.com.
#

##################

writeUACalcOp:=function(uacalcfile, op, opname)
#   Utility function for writing an operation to a file in uacalc 
#   format. The operation should be a vector of length N, say, containing integer 
#   values between 1 and N.  (These values will be converted to 0-offset.)
#
# INPUTS  uacalcfile = name of file to which operation should be written.
#         op = the operation (a vector)
#         opname = what to name the operation in the uacalc algebra file.
#
    local N, x;
    N:=Length(op);    
    AppendTo(uacalcfile, "<op>\n<opSymbol><opName>", opname, "</opName>\n");
    AppendTo(uacalcfile, "<arity>1</arity>\n</opSymbol>\n<opTable>\n<intArray>\n<row>");
    AppendTo(uacalcfile,op[1]-1);
    for x in [2..N] do
        AppendTo(uacalcfile, ",", op[x]-1);
    od;
    AppendTo(uacalcfile, "</row>\n</intArray>\n</opTable>\n</op>\n");
end;


##################

Overalgebra:=function(args)
    # Overalgebra:=function([G, [b1, b2,...], algebraname, EXTRAOPS])
    #
    # This function takes a transitive permutation group G acting on the set of moved points B0
    # and, for each bk in [b1, b2, ...], constructs a set BB[k], which has the single point 
    # bk in common with B0.  Then operations on the union A = B0 \cup BB[1] \cup BB[2] \cup ...
    # are defined to create an algebra on A, which is stored in a uacalc file named 
    # Overalgebra-algebraname-b1-b2-....ua.  Also, the original G-set algebra is stored in the same file
    # and called algebraname. (This can be turned off by setting the variable STORE_GSET:=false below.)
    #
    # Input   G              a transitive group on the set of moved points B0 = {1, 2, ..., N}
    #         [b1, b2, ...]  "tie-points" -- distinct points among the moved points of G;  bk = B0 \cap BB[k]
    #         algebraname    (optional, default=StructureDescription(G)) a string, used to name the uacalc algebra.
    #         EXTRAOPS       (optional, default=false) if true, add operations 
    #                        p_{g(k)} g p0 (x in BB[k]) for each g in setwise stabilizer of [b1, b2, ...].
    #
    # Output  Overalgebra-algebraname-b1-b2-....ua  A uacalc file which stores the original G-set algebra, called
    #                                      algebraname, as well as the Overalgebra-algebra <A, F> where A is the set 
    #                                      A = B0 \cup BB[1] \cup BB[2] \cup ... where 
    #                                            |B0| = |BB[1]| = |BB[2]| = ...,
    #                                            B0\cap BB[1] = {b1}, B0\cap BB[2] = {b2}, ...
    #                                            BB[i]\cap BB[j] = { }, unless i=j
    #                                      F is the set of maps:
    #                                            p0[k] maps A onto BB[k]
    #                                            s maps BB[k] onto bk and is the identity on B0
    #                                                      { g(c),  if c in B0
    #                                            gbar(c) = { (p1 g p0)(c), if c in B1
    #                                                      { (p2 g p0)(c), if c in B2

    local B0, BB, p0, s, gn, gensB, gensA, nargin, G, pathname, filename, outfile, N, opcount, g, k, z, x, pos, i, j, EXTRAOPS, XO, flag,
          b, axes, naxes, axstring, aboveax, VERBOSE, sizeA,algebraname, newops, genprod, uacalcpath, uacalcfile, STORE_GSET, e, numalgebras;
    
    ### Variables you can change to your liking:
    #
    uacalcpath := "./"; # For now, store output in current directory. 
                        # Change this, if you want, to something like
                        # uacalcpath := "/tmp/Overalgebras/";    
                        # but make sure the directory exists on your machine!!!

    VERBOSE:=false;         # Set this to false to supress extra command-line output.
    STORE_GSET:=true;      # Set this to false if you don't want the original G-set also stored in the uacalc file.
    #
    ###
    
    nargin := Length(args);
    if VERBOSE then
        Print("Overalgebra called with the following arguments: \n");
        for k in [1..nargin] do
            Print("args[",k,"] = ", args[k], "\n");
        od;
    fi;
    if nargin < 1 then 
        Error("Usage: Overalgebra([G, [b1, b2, ...], ...]);");
    else
        G:=args[1]; 
    fi;
    
    if nargin < 4 then EXTRAOPS:=false; XO:=false; else EXTRAOPS:=args[4]; XO:=args[4]; fi;
    if nargin < 3 then algebraname:=StructureDescription(G); else algebraname:=args[3]; fi;
    if nargin < 2 then Error("Usage: Overalgebra([G, [b1, b2, ...], ...);"); else axes:=args[2]; fi;
    
    # N.B. we now assume arguments passed in 0-offset notation!!!
    axes:=axes+1;
    
    naxes:=Length(axes);
    if not IsTransitive(G) then
        Error("Usage: Overalgebra([G, [b1, b2, ...], ...);  G must be a transitive group.");
    fi;
    
    
    axstring:=Concatenation("Overalgebra-", algebraname);
    for k in [1..naxes] do
        axstring:= Concatenation(axstring, "-", String(axes[k]-1));
    od;
    if XO then
        filename := Concatenation(uacalcpath, axstring, "-XO.ua");
    else
        filename := Concatenation(uacalcpath, axstring, ".ua");
    fi;

    Print("uacalc file: ", filename, "\n");
    uacalcfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(uacalcfile, false);   # prevents automatic indentation and line breaks.

    N:=NrMovedPoints(G);
    
    if VERBOSE then
        Print("axes = ", axes-1, "\n");
    fi;
    
    sizeA:= N+naxes*(N-1);
    B0:=[1..N];
    BB:=[];
    p0:=[];
    aboveax:=[];
    for k in [1..naxes] do
        Add(BB, [1..N]);
        Add(aboveax, 0);
        Add(p0, ());
    od;
    for b in B0 do
        for k in [1..naxes] do
            BB[k][b]:=b+(k*N)-(k-1)-aboveax[k];
        od;
        if b in axes then
            pos:=Position(axes, b);
            aboveax[pos]:=1;
            BB[pos][b]:=b;
        fi;
    od;
    if VERBOSE then
        Print("B0 = ", B0-1, "\n");
        for k in [1..naxes] do
            Print("B", k, " = ", BB[k]-1, "\n");
        od;
    fi;
    
    ### Construct the p0i's
    # Note: p0[k] maps B0 bijectively onto BB[k].
    # p0[k] is a permutation; e.g. p0[1]=(b1,b1')(b2,b2')...(bn,bn')
    # so you can apply it to any element x of A as follows:
    #  x^p0[k] will leave x fixed if x is not in B0 or BB[k]
    #          otherwise it will map x to the corresponding element of B0 or BB[k] 
    for b in B0 do
        for k in [1..naxes] do
            if b in axes then
                pos:=Position(axes, b);
                if k<>pos then
                    p0[k]:=p0[k]*(b,BB[k][b]); 
                fi;
            else
                p0[k]:=p0[k]*(b,BB[k][b]); 
            fi;
        od;
    od;        
    if VERBOSE then
        for k in [1..naxes] do
            Print("p0[", k, "] = ", p0[k], "\n");
        od;
    fi;
    
    ### Construct s  (maps BB[k] onto the kth axis, leaves B0 fixed)
    s:=[1..sizeA];
    for z in [1..sizeA] do
        for k in [1..naxes] do
            if z in BB[k] then
                s[z]:=axes[k]; 
                break;
            fi;
        od;
    od;
    if VERBOSE then Print("s = ", s-1, "\n");  fi;
    
    # now write the uacalc file
    PrintTo(uacalcfile, "<?xml version=\"1.0\"?>\n");
    
    if STORE_GSET or XO then   # there will be multiple algebras in the resulting uacalc file
        AppendTo(uacalcfile, "<algebraList>\n");
    fi;
    
    ### First put the original G-set algebra in the uacalc file 
    if STORE_GSET then
        AppendTo(uacalcfile, "<algebra>\n<basicAlgebra>\n<algName>", algebraname, "</algName>\n");
        AppendTo(uacalcfile, "<desc>The permutational algebra (", MovedPoints(G)-1, ", ", StructureDescription(G), ") (generated by Overalgebra).</desc>\n");
        AppendTo(uacalcfile, "<cardinality>", N, "</cardinality>\n");
        AppendTo(uacalcfile, "<operations>\n");
        opcount:=0;
    
        for g in GeneratorsOfGroup(G) do
            AppendTo(uacalcfile, "<op>\n<opSymbol><opName>g", opcount, "</opName>\n");
            AppendTo(uacalcfile, "<arity>1</arity>\n</opSymbol>\n<opTable>\n<intArray>\n<row>");
            AppendTo(uacalcfile, 1^g-1);
            for x in [2..N] do
                AppendTo(uacalcfile, ",", x^g-1);
            od;
            AppendTo(uacalcfile, "</row>\n</intArray>\n</opTable>\n</op>\n");
            opcount:=opcount+1;
        od;
        AppendTo(uacalcfile, "</operations>\n</basicAlgebra>\n</algebra>\n\n");
    fi;
    
    if XO then
        numalgebras:=2;   # Write 2 more algebras to the file, the 2nd with extra ops.
    else
        numalgebras:=1;   # Write just the one algebra (no extra ops)
    fi;
    
    for i in [1..numalgebras] do
        if i=2 then
            AppendTo(uacalcfile, "<algebra>\n<basicAlgebra>\n<algName>", axstring,"-XO</algName>\n");
            AppendTo(uacalcfile, "<desc>OveralgebraI on ", algebraname, " using points ", axes-1, " plus extra operations.</desc>\n");
        else
            AppendTo(uacalcfile, "<algebra>\n<basicAlgebra>\n<algName>", axstring,"</algName>\n");
            AppendTo(uacalcfile, "<desc>OveralgebraI on ", algebraname, " using points ", axes-1, ".</desc>\n");
        fi;
        AppendTo(uacalcfile, "<cardinality>", sizeA, "</cardinality>\n");
        AppendTo(uacalcfile, "<operations>\n");
    
        ## p0  N.B. we call this functions e_0 in the paper. ## 
        AppendTo(uacalcfile, "<op>\n<opSymbol><opName>e0</opName>\n");
        AppendTo(uacalcfile, "<arity>1</arity>\n</opSymbol>\n<opTable>\n<intArray>\n<row>");
        for z in [1..sizeA] do
            if z in B0 then
                AppendTo(uacalcfile, z-1, ",");  #  (this leaves extra comma in op definition -- hope that's ok)
            else
                for k in [1..naxes] do
                    if z in BB[k] then
                        AppendTo(uacalcfile, (z^p0[k])-1, ",");
                        break;
                    fi;
                od;
            fi;
        od;
        AppendTo(uacalcfile, "</row>\n</intArray>\n</opTable>\n</op>\n");
        
        ## p0[k]  N.B. we call these functions e_i in the paper. ## 
        for k in [1..naxes] do
            AppendTo(uacalcfile, "<op>\n<opSymbol><opName>e", k, "</opName>\n");
            AppendTo(uacalcfile, "<arity>1</arity>\n</opSymbol>\n<opTable>\n<intArray>\n<row>");
            for z in [1..sizeA] do
                if z in B0 then
                    AppendTo(uacalcfile, z^p0[k]-1, ",");
                else
                    for j in [1..naxes] do
                        if z in BB[j] then
                            if j=k then
                                AppendTo(uacalcfile, z-1, ",");
                            else
                                AppendTo(uacalcfile, (z^p0[j])^p0[k]-1, ",");
                            fi;
                            break;
                        fi;
                    od;
                fi;
            od;
            AppendTo(uacalcfile, "</row>\n</intArray>\n</opTable>\n</op>\n");
        od;
    
        AppendTo(uacalcfile, "<op>\n<opSymbol><opName>s</opName>\n");
        AppendTo(uacalcfile, "<arity>1</arity>\n</opSymbol>\n<opTable>\n<intArray>\n<row>");
        AppendTo(uacalcfile, s[1]-1);
        for z in [2..sizeA] do AppendTo(uacalcfile, ",", s[z]-1); od;
        AppendTo(uacalcfile, "</row>\n</intArray>\n</opTable>\n</op>\n");
    
        opcount:=0;
        # now construct the operations g p_0, one for each generator g of G.
        for g in GeneratorsOfGroup(G) do
            AppendTo(uacalcfile, "<op>\n<opSymbol><opName>g", opcount, "</opName>\n");
            AppendTo(uacalcfile, "<arity>1</arity>\n</opSymbol>\n<opTable>\n<intArray>\n<row>");
            for z in [1..sizeA] do
                if z in B0 then
                    AppendTo(uacalcfile, z^g-1,",");
                else
                    for k in [1..naxes] do
                        if z in BB[k] then
                            AppendTo(uacalcfile,(z^p0[k])^g-1, ",");
                            break;
                        fi;
                    od;
                fi;
            od;
            AppendTo(uacalcfile, "</row>\n</intArray>\n</opTable>\n</op>\n");
            opcount:=opcount+1;
        od;
        
        # extra operations (only write these on the second pass)        
        if i=2 then
            opcount:=1;
            for g in Elements(G) do
                if g=() then
                    # do nothing
                else
                    flag:=1;
                    # check if g stabilizes the set of axes
                    for b in axes do
                        if b^g in axes then
                        else
                            flag:=0;
                            break;
                        fi;
                    od;
                    if flag=1 then
                        if VERBOSE then Print("Stab(axes) element g = ", g, "\n");  fi;
                        AppendTo(uacalcfile, "<op>\n<opSymbol><opName>g^pi_", opcount, "</opName>\n");
                        AppendTo(uacalcfile, "<arity>1</arity>\n</opSymbol>\n<opTable>\n<intArray>\n<row>");
                        if VERBOSE then  Print("g^pi_", opcount, "="); fi;
                        for z in [1..sizeA] do
                            if z in B0 then
                                AppendTo(uacalcfile, z^g-1,",");
                                if VERBOSE then  Print(z^g-1,","); fi;
                            else
                                for k in [1..naxes] do
                                    if z in BB[k] then
                                        # find out to which axis g moves kth axis
                                        b := axes[k]^g;
                                        pos:=Position(axes, b);
                                        AppendTo(uacalcfile,(((z^p0[k])^g)^p0[pos])-1, ","); 
                                        if VERBOSE then Print((((z^p0[k])^g)^p0[pos])-1,","); fi;
                                        break;
                                    fi;
                                od;
                            fi;
                        od;
                        AppendTo(uacalcfile, "</row>\n</intArray>\n</opTable>\n</op>\n");
                        if VERBOSE then Print("\n"); fi;
                        opcount:=opcount+1;
                    fi;
                fi;
            od;
        fi;
        AppendTo(uacalcfile, "</operations>\n</basicAlgebra>\n</algebra>\n");
    od;
    if STORE_GSET or XO then
        AppendTo(uacalcfile, "</algebraList>\n");
    fi;
    
end;


##################

OveralgebraXO:=function(args)
    # OveralgebraXO:=function([G, [ [a1, a2,...],[b1, b2,...],...,[c1, c2,...] ], algebraname])
    #

    local B0, BB, e, e0, s, ss, ge0, gn, gensB, gensA, nargin, G, gens, numgens, pathname, filename, outfile, N, opcount, g, k, z, x, pos, i, j, 
          flag, b, axes, naxes, AXES, naxesSets, axstring, namestring, VERBOSE, sizeA,algebraname, newops, genprod, uacalcpath, 
          uacalcfile, STORE_GSET, numalgebras, AC, opname, Bmp, tmp;
    
    ### Variables you can change to your liking:
    #
    uacalcpath := "./"; # For now, store output in current directory. 
                        # Change this, if you want, to something like
                        # uacalcpath := "/tmp/Overalgebras/";    
                        # but make sure the directory exists on your machine!!!

    VERBOSE:=false;         # Set this to false to supress extra command-line output.
    STORE_GSET:=true;      # Set this to false if you don't want the original G-set also stored in the uacalc file.
    #
    ###
    
    nargin := Length(args);
    if VERBOSE then
        Print("OveralgebraXO called with the following arguments: \n");
        for k in [1..nargin] do
            Print("args[",k,"] = ", args[k], "\n");
        od;
    fi;
    if nargin < 1 then 
        Error("Usage: OveralgebraXO([G, [[a1, a2,...],[b1, b2,...],...,[c1, c2,...]], ...]);");
    else
        G:=args[1]; 
    fi;
    
    if nargin < 3 then algebraname:=StructureDescription(G); else algebraname:=args[3]; fi;
    if nargin < 2 then Error("Usage: OveralgebraXO([G, [b1, b2, ...], ...);"); else AXES:=args[2]; fi;
    
    # N.B. we now assume arguments passed in 0-offset notation!!!
    AXES:=AXES+1;
    
    naxesSets:=Length(AXES);
    if not IsTransitive(G) then
        Error("Usage: OveralgebraXO([G, [ [a1, a2,...],[b1, b2,...],...,[c1, c2,...] ],...);  G must be a transitive group.");
    fi;
    
    naxes:=0;
    axes:=[];
    namestring:=Concatenation("OveralgebraXO-", algebraname);
    axstring:="";
    for j in [1..naxesSets] do
        naxes:=naxes+Length(AXES[j]);  # number of axes counting multiplicity
        for k in [1..Length(AXES[j])] do
            Add(axes, AXES[j][k]);
            axstring:= Concatenation(axstring, String(AXES[j][k]-1));
            if k<>Length(AXES[j]) then
                axstring:= Concatenation(axstring, "-");
            fi;
        od;
        if j<>naxesSets then
            axstring:= Concatenation(axstring, "_");
        fi;
    od;
    
    filename := Concatenation(uacalcpath, namestring, "_", axstring, ".ua");
    
    if Length(axes)<>naxes then
        Error("unexpected number of axes");
    fi;
    
    Print("uacalc file: ", filename, "\n");
    uacalcfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(uacalcfile, false);   # prevents automatic indentation and line breaks.

    Bmp:=MovedPoints(G);
    N:=NrMovedPoints(G);
    
    if VERBOSE then
        Print("AXES = ", AXES-1, "\n");
    fi;
    
    sizeA:= N+naxes*(N-1);
    B0:=[1..N];
    BB:=[];
    AC:=0;  # running axis count
    for j in [1..naxesSets] do
        for k in [1..Length(AXES[j])] do 
            AC:=AC+1;
            BB[AC]:=[];
            tmp:=[AC*N-(AC-2)..AC*N+N-AC];
            pos:=Position(B0, AXES[j][k]);
            Append(BB[AC], tmp{[1..pos-1]});
            Add(BB[AC], AXES[j][k]);
            Append(BB[AC], tmp{[pos..N-1]});
        od;
    od;
    if VERBOSE then
        Print("B0 = ", B0-1, "\n");
        for k in [1..naxes] do
            Print("BB[", k, "] = ", BB[k]-1, "\n");
        od;
    fi;
    # construct e0
    e0:=[1..sizeA];
    for j in [1..naxes] do
        for b in BB[j] do
            pos:=Position(BB[j], b);
            e0[b]:=B0[pos];
        od;
    od;

    # construct the e[k] 0\leq k \leq naxes
    e:=[];
    for k in [1..naxes] do
        e[k]:=[1..sizeA];
        for b in B0 do
            pos:=Position(B0, b);
            e[k][b]:=BB[k][pos];
        od;
        for j in [1..naxes] do
            for b in BB[j] do
                if b in B0 then
                    # do nothing
                else
                    pos:=Position(BB[j], b);
                    e[k][b]:=BB[k][pos];
                fi;
            od;
        od;
    od;
    if VERBOSE then
        Print("e[0] = ", e0-1, "\n");
        for k in [1..naxes] do
            Print("e[", k, "] = ", e[k]-1, "\n");
        od;
    fi;
    
    ### Construct s  (maps BB[k] onto the kth axis, leaves B0 fixed)
    s:=[1..sizeA];
    for z in [1..sizeA] do
        for k in [1..naxes] do
            if z in BB[k] then
                s[z]:=axes[k]; 
                break;
            fi;
        od;
    od;
    if VERBOSE then Print("s = ", s-1, "\n");  fi;
    
    ## construct new operations ss[k] ##
    ss:=[];
    AC:=0;  # running axis count
    for j in [1..naxesSets] do
        ss[j]:=[1..sizeA];
        for k in [1..Length(AXES[j])] do 
            AC:=AC+1;
            for b in BB[AC] do
                ss[j][b]:=AXES[j][k];
            od;
        od;
    od;
    if VERBOSE then
        for k in [1..naxesSets] do
            Print("s[", k, "] = ", ss[k]-1, "\n");
        od;
    fi;
    
    ### Construct g e0, one for each g in G.
    ge0:=[];
    gens:=GeneratorsOfGroup(G);
    numgens:=Length(gens);
    for i in [1..numgens] do
        ge0[i]:=[1..sizeA];
        g:=gens[i];
        for j in [1..sizeA] do            
            x:=Bmp[e0[j]]^g;              # The p0[j]-th moved point is moved to x; 
            ge0[i][j]:=Position(Bmp, x);  # gp0[i][x]:= the index of x in Bmp.
        od;
        if VERBOSE then
            Print("g[", i, "]e0 = ", ge0[i]-1, "\n");
        fi;
    od;
    
    # now write the uacalc file
    PrintTo(uacalcfile, "<?xml version=\"1.0\"?>\n");
            
    if STORE_GSET then   # there will be multiple algebras in the resulting uacalc file
        AppendTo(uacalcfile, "<algebraList>\n");
    fi;
            
    ### First put the original G-set algebra in the uacalc file 
    if STORE_GSET then
        AppendTo(uacalcfile, "<algebra>\n<basicAlgebra>\n<algName>", algebraname, "</algName>\n");
        AppendTo(uacalcfile, "<desc>The permutational algebra (", MovedPoints(G)-1, ", ", StructureDescription(G), ") (generated by OveralgebraXO).</desc>\n");
        AppendTo(uacalcfile, "<cardinality>", N, "</cardinality>\n");
        AppendTo(uacalcfile, "<operations>\n");
        opcount:=0;
    
        for g in GeneratorsOfGroup(G) do
            AppendTo(uacalcfile, "<op>\n<opSymbol><opName>g", opcount, "</opName>\n");
            AppendTo(uacalcfile, "<arity>1</arity>\n</opSymbol>\n<opTable>\n<intArray>\n<row>");
            AppendTo(uacalcfile, 1^g-1);
            for x in [2..N] do
                AppendTo(uacalcfile, ",", x^g-1);
            od;
            AppendTo(uacalcfile, "</row>\n</intArray>\n</opTable>\n</op>\n");
            opcount:=opcount+1;
        od;
        AppendTo(uacalcfile, "</operations>\n</basicAlgebra>\n</algebra>\n\n");
    fi;
    
    # Now write the general overalgebra
    AppendTo(uacalcfile, "<algebra>\n<basicAlgebra>\n<algName>",namestring,"</algName>\n");
    AppendTo(uacalcfile, "<desc>Overalgebra on ", algebraname, " using points ", axstring,".</desc>\n");
    AppendTo(uacalcfile, "<cardinality>", sizeA, "</cardinality>\n");
    AppendTo(uacalcfile, "<operations>\n");
    
    ## e0  ##
    writeUACalcOp(uacalcfile, e0, "e0");
    
    ## e[k] ##
    for k in [1..naxes] do
        opname:=Concatenation("e",String(k));
        writeUACalcOp(uacalcfile, e[k], opname);
    od;    
    ## s ##
    writeUACalcOp(uacalcfile, s, "s");
    
    for k in [1..naxesSets] do
        opname:=Concatenation("s",String(k));
        writeUACalcOp(uacalcfile, ss[k], opname);
    od;
    
    ## gie0  ##
    for i in [1..numgens] do
        opname:=Concatenation("g",String(i),"e0");
        writeUACalcOp(uacalcfile, ge0[i], opname);
    od;
    
    AppendTo(uacalcfile, "</operations>\n</basicAlgebra>\n</algebra>\n");

    if STORE_GSET then
        AppendTo(uacalcfile, "</algebraList>\n");
    fi;
        
end;


##################

Overalgebra2:=function(args)
    # Overalgebra2:=function([G, [[a1,b1],[a2,b2],...,[ak,bk]], algebraname])
    #
    # This function takes a transitive permutation group G acting on a set of N moved points
    # B={1,2,...,N}, and a list of pairs of points in this set, [[a1,b1],[a2,b2],...,[ak,bk]]
    # with ai<>bi, and for each 1<i<k+1, constructs a set BB[i], which is in bijective 
    # correspondence with B via pp[i]:B-->BB[i] and so that, for 1<i<k-1, 
    # 
    #     BB[i] \ni pp[i][b[i]] = pp[i+1][a[i+1]]  \in BB[i+1],
    #
    #     B \ni a[1] = pp[1][a[1]]  \in BB[1], and
    #
    #     BB[k] \ni pp[k][b[k]] = pp[k+1][a[1]]  \in BB[k+1], and
    #
    # and the sets have no other points in common, other than the ones mentioned above.
    #
    # Then operations on the union A = B0 \cup BB[1] \cup BB[2] \cup ...
    # are defined to create an algebra on A, which is stored in a uacalc file named 
    # Overalgebra2-algebraname.ua.  Also, the original G-set algebra is stored in the same file
    # and called algebraname. (This can be turned off by setting the variable STORE_GSET:=false below.)
    #
    # Input   G              a transitive group on the set of moved points B0 = {1, 2, ..., N}
    #         [[a1,b1],[a2,b2],...,[ak,bk]]  the tie-points
    #         algebraname    (optional, default=StructureDescription(G)) a string, used to name the uacalc algebra.
    #
    # Output  Overalgebra2-algebraname.ua  A uacalc file which stores the original G-set algebra, called
    #                             algebraname, as well as the Overalgebra2-algebra <A, F> where A is the set 
    #                                      A = B0 \cup BB[1] \cup BB[2] \cup ...
    #                                      F is the set of maps:
    #                                         (fill this in later)
    #
    # Example    gap> Read("Overalgebras.g");
    #            gap> G:=TransitiveGroup(12,7);
    #            gap> for b in AllBlocks(G) do Print(Orbit(G,b,OnSets), "\n"); od;
    #            [ [ 1, 3, 5, 7, 9, 11 ], [ 2, 4, 6, 8, 10, 12 ] ]
    #            [ [ 1, 6 ], [ 7, 12 ], [ 5, 10 ], [ 4, 11 ], [ 2, 9 ], [ 3, 8 ] ]
    #            [ [ 1, 6, 7, 12 ], [ 4, 5, 10, 11 ], [ 2, 3, 8, 9 ] ]            <--- non-principal coatom
    #            [ [ 1, 7 ], [ 5, 11 ], [ 3, 9 ], [ 6, 12 ], [ 4, 10 ], [ 2, 8 ] ]
    #            [ [ 1, 12 ], [ 6, 7 ], [ 4, 5 ], [ 10, 11 ], [ 8, 9 ], [ 2, 3 ] ]
    #
    #            Pick your a1, ..., ak, b1, ..., bk, say, [a1,b1]=[1, 6], [a2,b2]=[1, 7]
    #            and run the Overalgebra2 function like this:
    #
    #            gap> Overalgebra2( [ G, [[1,6],[1,7]] ] );
    # 
    #            This produces a file called Overalgebra2-C2 x A4_1-6_1-7.ua.

    local i, j, k, z, x, K, aa, a, bb, b, bi, bj, blk, Bmp, B0, B1, BB, p0, p, pi, r, q, g, gp0, gens, Gens, numgens, N, n, 
          nargin, G, pathname, filename, outfile, opcount, pos, VERBOSE, sizeA, algebraname, opname,
          uacalcpath, uacalcfile, STORE_GSET, numalgebras, yetfound;
    
    ### Variables you can change to your liking:
    uacalcpath := "./"; # <<< ATTENTION! This is where uacalc file is stored.
    VERBOSE:=true;         # Set this to false to supress extra command-line output.
    STORE_GSET:=true;      # Set this to false if you don't want the original G-set also stored in the uacalc file.
    ###
    
    nargin := Length(args);
    if VERBOSE then
        Print("Overalgebra2 called with the following arguments: \n");
        for k in [1..nargin] do
            Print("args[",k,"] = ", args[k], "\n");
        od;
    fi;
    
    if nargin < 2 then 
        Error("Usage: Overalgebra2([G, [[a1,b1], [a2,b2],...],  algebraname])"); 
    else 
        G:=args[1];  
        Gens:=args[2];   # The generators, or axes, as a list of lists: [[a1,b1], [a2,b2], ...]
    fi;
    
    # N.B. we now assume arguments passed in 0-offset notation!!!
    Gens:=Gens+1;    
    
    K:=Length(Gens);
    aa:=[];
    bb:=[];
    for k in [1..K] do
        Add(aa,Gens[k][1]);
        Add(bb,Gens[k][2]);
    od;
    if nargin < 3 then algebraname:=StructureDescription(G); else algebraname:=args[3]; fi;

    if not IsTransitive(G) then
        Error("Usage: Overalgebra2([G, ...]);  G must be a transitive group.");
    fi;
    
    filename:=Concatenation(uacalcpath, "Overalgebra2_", algebraname, "_");
    
    # TODO(wjd): probably don't need the next line.
    K:=Length(aa);   
    
    for k in [1..K] do
        filename:= Concatenation(filename, String( aa[k] - 1 ), "-", String( bb[k] - 1));
        if k<>K then filename:= Concatenation(filename, "_"); fi;
    od;
    filename:=Concatenation(filename, ".ua");
    
    if VERBOSE then Print("\nuacalc file: ", filename, "\n"); fi;
    uacalcfile := OutputTextFile(filename, false);
    SetPrintFormattingStatus(uacalcfile, false);   # prevents automatic indentation and line breaks.

    Bmp:=MovedPoints(G);
    N:=NrMovedPoints(G);
    for k in [1..K] do
        if not (aa[k] in Bmp) then
            Error("Usage: Overalgebra2([G, [[a1,b1],...,[ak,bk]],...]);  a_",k," must be in the set B=MovedPoints(G)."); 
        fi;
        if not (bb[k] in Bmp) then
            Error("Usage: Overalgebra2([G, [[a1,b1],...,[ak,bk]],...]);  b_",k," must be in the set B=MovedPoints(G)."); 
        fi;
        if aa[k]=bb[k] then
            Error("Usage: Overalgebra2([G, [[a1,b1],...,[ak,bk]],...]);  a",k,"=b",k,", but they must be distinct."); 
        fi;
    od;
    
    # Print the congruences and tie-points
    if VERBOSE then
        Print("\n--- CONGRUENCES of (B,G) --- \n");
        for blk in AllBlocks(G) do Print(Orbit(G,blk,OnSets), "\n"); od;
        Print("\ntie-points: a=", aa, ";  b=", bb, ";\n"); 
    fi;
    
    a:=[];  b:=[];    # the indices of the aa and bb in the set of moved points.
    for k in [1..K] do
        a[k]:=Position(Bmp,aa[k]);
        b[k]:=Position(Bmp,bb[k]);
    od;
    
    sizeA:= (K+2)*N-(K+1);
    B0:=[1..N];    # (indices of) the elements in original universe (the moved points of G)
    BB:=[];        # The rows of BB are B1, B2, B3, ...
    BB[1]:=B0+N;   # BB[1] = the left hand rabbit ear
    BB[1][a[1]]:=a[1];
    for j in [(a[1]+1)..N] do
        BB[1][j]:=BB[1][j]-1;
    od;
    for i in [2..K] do
        BB[i]:=[1..N]+BB[i-1][N];
        BB[i][a[i]]:=BB[i-1][b[i-1]];
        for j in [(a[i]+1)..N] do
            BB[i][j]:=BB[i][j]-1;
        od;
    od;
    BB[K+1]:=[1..N]+BB[K][N];
    BB[K+1][a[1]]:=BB[K][b[K]];
    for j in [(a[1]+1)..N] do                          
        BB[K+1][j]:=BB[K+1][j]-1;
    od;
    
    if VERBOSE then
        Print("\n--- MINIMAL SETS --- \n");
        Print("B0    = ", B0-1, "\n");
        for k in [1..K+1] do
            Print("BB[", k, "] = ", BB[k]-1, "\n");
        od;
    fi;
    
    if VERBOSE then
        Print("\nThe size of A is ", sizeA,". This should equal BB[K+1][N]=BB[",K+1,"][",N,"]=",BB[K+1][N],"\n");
        if BB[K+1][N]<>sizeA then
            Print("\nWARNING: the equality above is false, so we got the size of A wrong.\n");
        fi;
    fi;
    p0:=[];
    
    ### Construct p0 and r ###
    r:= [1..sizeA];
    p:=[];
    p[K+1]:=[1..sizeA];
    for x in [1..sizeA] do
        if x in B0 then
            p0[x]:=x;
            p[K+1][x]:=BB[K+1][x];
            r[x]:=a[1];
        elif x in BB[K+1] then
            p0[x]:=Position(BB[K+1], x);
            p[K+1][x]:=x;
            r[x]:=BB[K+1][a[1]];
        else
            p0[x]:=a[1];                     
            p[K+1][x]:=BB[K+1][a[1]];          
            r[x]:=x;
        fi;
    od;
    
    ### Construct the pi's
    for k in [1..K] do  #for k in [2..K] do
        p[k]:=[1..sizeA];
        for x in [1..sizeA] do
            if x in BB[k] then
                p[k][x]:=x;
            elif x < BB[k][1] or x< BB[k][2] # we have to check two since on of them could be the intersection point
              then  
                p[k][x]:=BB[k][a[k]];
            elif x > BB[k][N] then
                p[k][x]:=BB[k][b[k]];
            else
                Print("\nWARNING: Didn't expect to get here... There must be an error.\n");
            fi;
        od;
    od;        
    
    ### Construct the qij = sij pi
    q:=[];
    for i in [0..K+1] do
        q[i+1]:=[];
        if i=0 then 
            bi:=B0; pi:=p0; 
        else 
            bi:=BB[i]; pi:=p[i];
        fi;
        for j in [0..K+1] do
            if j=0 then bj:=B0; else bj:=BB[j]; fi;
            q[i+1][j+1]:=[1..sizeA];
            for x in [1..sizeA] do
                q[i+1][j+1][x]:=bj[Position(bi,pi[x])];
            od;
        od;
    od;
    
    ### Construct g p0, one for each g in G.
    gp0:=[];
    gens:=GeneratorsOfGroup(G);
    numgens:=Length(gens);
    for i in [1..numgens] do
        gp0[i]:=[1..sizeA];
        g:=gens[i];
        for j in [1..sizeA] do            
            x:=Bmp[p0[j]]^g;              # The p0[j]-th moved point is moved to x; 
            gp0[i][j]:=Position(Bmp, x);  # gp0[i][x]:= the index of x in Bmp.
        od;
    od;
    
    if VERBOSE then
        Print("\n--- OPERATIONS ---\n");
        Print("\nr = ", r, "\n");
        Print("\n------ pi's --------\n");
        Print("p0 = ", p0, "\n");
        for k in [1..K+1] do
            Print("p[", k, "] = ", p[k], "\n");
        od;
        Print("\n------ qij's --------\n");
        for i in [1..K+1] do
            for j in [1..K+1] do
                Print("q[", i, "][", j, "] = ", q[i][j], "\n");
            od;
        od;
        Print("\n------ gip0's --------\n");
        for i in [1..numgens] do
            Print("g", i, "p0 = ", gp0[i], "\n");
        od;
    fi;
    
    # now write the uacalc file
    PrintTo(uacalcfile, "<?xml version=\"1.0\"?>\n");
            
    if STORE_GSET then  ### First put the original G-set algebra in the uacalc file 
        AppendTo(uacalcfile, "<algebraList>\n");
        AppendTo(uacalcfile, "<algebra>\n<basicAlgebra>\n<algName>", algebraname, "</algName>\n");
        AppendTo(uacalcfile, "<desc>The permutational algebra (", MovedPoints(G)-1, ", ", StructureDescription(G), ") (generated by Overalgebra2).</desc>\n");
        AppendTo(uacalcfile, "<cardinality>", N, "</cardinality>\n");
        AppendTo(uacalcfile, "<operations>\n");
        
        for i in [1..numgens] do
            g:=gens[i];
            AppendTo(uacalcfile, "<op>\n<opSymbol><opName>g", i, "</opName>\n");
            AppendTo(uacalcfile, "<arity>1</arity>\n</opSymbol>\n<opTable>\n<intArray>\n<row>");
            for j in [1..N] do
                x:=Bmp[j]^g;
                x:=Position(Bmp, x);
                AppendTo(uacalcfile, x-1, "," );
            od;
            AppendTo(uacalcfile, "</row>\n</intArray>\n</opTable>\n</op>\n");
        od;
        AppendTo(uacalcfile, "</operations>\n</basicAlgebra>\n</algebra>\n\n");
    fi;
    
    # Now write the general overalgebra
    AppendTo(uacalcfile, "<algebra>\n<basicAlgebra>\n<algName>Overalgebra2-", algebraname,"</algName>\n");
    AppendTo(uacalcfile, "<desc>OveralgebraII on ", algebraname, " using points ", Gens-1,".</desc>\n");
    AppendTo(uacalcfile, "<cardinality>", sizeA, "</cardinality>\n");
    AppendTo(uacalcfile, "<operations>\n");
    
    ## p0  N.B. we call this functions e_0 in the paper. ## 
    writeUACalcOp(uacalcfile, p0, "e0");
    
    ## p0[k]  N.B. we call these functions e_i in the paper. ## 
    for k in [1..K+1] do
        opname:=Concatenation("e",String(k));
        writeUACalcOp(uacalcfile, p[k], opname);
    od;    
    ## r ##
    writeUACalcOp(uacalcfile, r, "r");
    
    ## gip0  N.B. we call these functions g_i e_0 in the paper. ##
    for i in [1..numgens] do
        opname:=Concatenation("g",String(i),"e0");
        writeUACalcOp(uacalcfile, gp0[i], opname);
    od;
    
    ## qij = sij pi  ##
    for i in [0..K+1] do
        for j in [0..K+1] do
            opname:=Concatenation("q_",String(i),",", String(j));
            writeUACalcOp(uacalcfile, q[i+1][j+1], opname);
        od;
    od;
    
    AppendTo(uacalcfile, "</operations>\n</basicAlgebra>\n</algebra>\n");

    if STORE_GSET then
        AppendTo(uacalcfile, "</algebraList>\n");
    fi;
end;    


# You can run the examples in GAP as follows:
#
#    gap> Read("Overalgebras.g");
#    gap> OveralgebraExample(1);  # Example 3.1 in the paper
#    gap> OveralgebraExample(2);  # Example 3.2
#    gap> OveralgebraExample(3);  # Example 3.3
#
OveralgebraExample:=function(number)
    local G, act, b, x, g;
    Read("Overalgebras.g");
    # Start with the right regular S3-set.
    g:=Group([(1,2), (1,2,3)]);
    x:=[(),(1,2,3),(1,3,2),(1,2),(1,3),(2,3)];
    G:=Action(g,x,OnRight);
    
    #### Example 3.1 ####
    if number=1 then

        # View the congruences of the S3-set.
        for b in AllBlocks(G) do Print(Orbit(G,b,OnSets)-1, "\n"); od;

        # Create an overalgebra with tie-points T={0, 2}.
        Overalgebra([G, [0,2]]);

        # Create an overalgebra with tie-points T={0, 3}.
        Overalgebra([G, [0,3]]);
        
    #### Example 3.2 ####
    elif number=2 then
        
        # View the congruences of the S3-set.
        for b in AllBlocks(G) do Print(Orbit(G,b,OnSets)-1, "\n"); od;

        # Create an overalgebra with tie-points T={0, 1}.
        Overalgebra([G, [0,1]]);

        # Create an overalgebra with tie-points T={0, 1, 2}.
        Overalgebra([G, [0,1,2]]);

        # Create an overalgebra with tie-points T={0, 1, 2, 3}.
        Overalgebra([G, [0,1,2,3]]);

        # Create an overalgebra with tie-points T={0, 2, 3}.
        Overalgebra([G, [0,2,3]]);
        
        # Create an overalgebra with tie-points T={0, 2, 3, 5}.
        Overalgebra([G, [0,2,3,5]]);
        
        # Create an overalgebra with tie-points T = {0, 1} U {2, 3}.
        OveralgebraXO([ G, [[0,1],[2,3]] ]);
        
        # Create an overalgebra with tie-points T = {0, 1} U {0, 2}.
        OveralgebraXO([ G, [[0,1],[0,2]] ]);
        
        # Create an overalgebra with tie-points T = {0, 1} U {1, 2}.
        OveralgebraXO([ G, [[0,1],[1,2]] ]);
        
        # Create an overalgebra with tie-points T = {0, 1} U {0, 1} U {0, 1} U {0, 1}.
        OveralgebraXO([ G, [[0,1],[0,1],[0,1],[0,1]] ]);
        
        # Create an overalgebra with tie-points T={0, 1, 2}
        OveralgebraXO([G, [[0,1,2]]]);
        
        # Create an overalgebra with tie-points T={0, 1, 2} U {3, 4, 5}
        OveralgebraXO([G, [[0,1,2],[3,4,5]]]);
        
        # Create an overalgebra with tie-points T={0, 1, 2} U {0, 1, 2} U {3, 4, 5}
        OveralgebraXO([G, [[0,1,2],[0,1,2], [3,4,5]]]);

        # Create an overalgebra with tie-points T = {0, 3} U {2, 5}.
        OveralgebraXO([ G, [[0,3],[2,5]] ]);
        
        # Create an overalgebra with tie-points T = {0, 3} U {0, 3}
        OveralgebraXO([ G, [[0,3],[0,3]] ]);
        
        # Create an overalgebra with tie-points T = {0, 3} U {0, 3} U {0, 3}
        OveralgebraXO([ G, [[0,3],[0,3], [0,3]] ]);
        
        # Create an overalgebra with tie-points T = {0, 3} U {0, 3} U {0, 3}
        OveralgebraXO([ G, [[0,3],[0,3], [0,3], [0,3]] ]);
        
        # Create an overalgebra with tie-points T = {0, 3} U {0, 3} U {2, 5}
        OveralgebraXO([ G, [[0,3],[0,3],[2,5]] ]);
        
        
    #### Example 3.3 ####        
    elif number=3 then
        
        # start with the transitive group C2 x A4
        G:=Group([(9,10)(11,12)(5,6)(7,8), 
                  (3,7,12)(9,1,6)(11,4,8)(5,10,2), 
                  (3,2)(9,11)(5,7)(1,4)(10,12)(6,8)]);
        # Same group as G:=TransitiveGroup(12,7), but we define as
        # above so that the blocks of the congruences look nicer.

        # View the congruences of the S3-set.
        for b in AllBlocks(G) do Print(Orbit(G,b,OnSets)-1, "\n"); od;
        
        # Create an overalgebra with tie-points (0, 3).
        Overalgebra([G, [0,3]]);
        
        # Create an 2nd generation overalgebra with tie-points (0, 3), (8,11).
        Overalgebra2([G, [[0,3], [8,11]]]);
    fi;
end;


        
