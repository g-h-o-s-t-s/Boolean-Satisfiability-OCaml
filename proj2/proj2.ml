open Proj2_types;;

(*-------------------------------------------------------------------------*)

let addUnique i l = 
    if List.mem i l then l 
    else i::l
;;

let removeDuplicates l = 
    List.fold_right addUnique l []
;;

let scanVariable (input : string list) : string list = 

    List.filter (fun x ->
             x = "a" || x = "b" || x = "c" || x = "d"
            || x = "e" || x = "f" || x = "g" || x = "h"
            || x = "i" || x = "j" || x = "k" || x = "l"
            || x = "m" || x = "n" || x = "o" || x = "p"
            || x = "q" || x = "r" || x = "s" || x = "t"
            || x = "u" || x = "v" || x = "w" || x = "x" 
            || x = "y" || x = "z")
    (removeDuplicates input)
;;

(*-------------------------------------------------------------------------*)

let generateInitialAssignList (varList : string list) : (string * bool) list =
    
    let rec producePairs l = 
        match l with
        | [] -> []
        | head::rest -> (head, false) :: producePairs rest

    in
    producePairs varList
;;

(*-------------------------------------------------------------------------*)

let determineVar str bl = 
    if snd str = false
        then
        (
            if bl = false then (fst str, false)
            else (fst str, true)
        )
    else
        if bl = false then (fst str, true)
        else (fst str, false)
;;

let determineCarry str bl = 
    if snd str = false then false
    else
        if snd str = true
            then
            (
                if bl = false then false
                else true
            )
        else false
;;

let generateNextAssignList (assignList : (string * bool) list) : (string * bool) list * bool = 

    let rec genNext l acc bl = 
        match l with
        | [] -> (acc, bl)
        | (head::rest) -> genNext rest ((determineVar head bl)::acc) (determineCarry head bl)

    in 
    genNext (List.rev assignList) [] true
;;

(*-------------------------------------------------------------------------*)

let lookupVar (assignList : (string * bool) list) (str : string) : bool =
    
    if assignList = []
        then raise (Invalid_argument "Empty list.")
        else 
            List.assoc str assignList
;;

(*-------------------------------------------------------------------------*)

let rec evaluateTree (t : tree) (assignList : (string * bool) list) : bool = 

    match t with
    | TreeNode ("and", hd::tl) -> (evaluateTree hd assignList) 
                                && (evaluateTree (List.hd tl) assignList)
    | TreeNode ("or", hd::tl) -> (evaluateTree hd assignList) 
                                || (evaluateTree (List.hd tl) assignList)
    | TreeNode ("not", lst) -> not (evaluateTree (List.hd lst) assignList)
    | TreeNode ("TRUE", []) -> true
    | TreeNode ("FALSE", []) -> false
    | TreeNode (str, []) -> lookupVar assignList str
    | TreeNode (_, _) -> raise (Invalid_argument "Unacceptable input for given grammar.")
;;

(*-------------------------------------------------------------------------*)

let parseTerminal str sList = (TreeNode (str, []), List.tl sList);;

let buildParseTree (input : string list) : tree = 

    let rec parseNonTerminal str sList = 
        if str = "("
            then
            (
                let left = parseTerminal "(" sList in
                let middle = parseNonTerminal "T" (snd left) in 
                let right = parseTerminal ")" (snd middle) in 
                (TreeNode ("S", [fst left; fst middle; fst right]), snd right)
            )
        else
            if str = "T" 
                then 
                ( 
                    match List.hd sList with
                    | "not" -> (
                        let left = parseTerminal "not" sList in
                        let right = parseNonTerminal "S" (snd left) in 
                        ( TreeNode ("T", [fst left; fst right]), snd right) )

                    | "and" -> (
                        let left = parseTerminal "and" sList in
                        let middle = parseNonTerminal "S" (snd left) in
                        let right = parseNonTerminal "S" (snd middle) in
                        ( TreeNode ("T", [fst left; fst middle; fst right]), snd right) )

                    | "or" -> (
                        let left = parseTerminal "or" sList in
                        let middle = parseNonTerminal "S" (snd left) in
                        let right = parseNonTerminal "S" (snd middle) in
                        ( TreeNode ("T", [fst left; fst middle; fst right]), snd right) )

                    | _-> raise (Invalid_argument "Unacceptable input for given grammar.")
                )
            else
                if str = "S"
                    then
                    (
                        match List.hd sList with
                        | "(" -> (
                            parseNonTerminal "(" sList
                        )
                        | (str2:string) -> (
                            let term = parseTerminal str2 sList in
                            (TreeNode ("S", [fst term]), snd term)
                        )
                    )
                else 
                    if ( str = "a" || str = "b" || str = "c" || str = "d"
                        || str = "e" || str = "f" || str = "g" || str = "h"
                        || str = "i" || str = "j" || str = "k" || str = "l"
                        || str = "m" || str = "n" || str = "o" || str = "p"
                        || str = "q" || str = "r" || str = "s" || str = "t"
                        || str = "u" || str = "v" || str = "w" || str = "x" 
                        || str = "y" || str = "z" || str = "TRUE" || str = "FALSE" ) 

                        then (TreeNode ("S", [TreeNode(str, [])]), []) 
                    else raise (Invalid_argument "Unacceptable input for given grammar.")
    in

    fst (parseNonTerminal (List.hd input) input)
;;

(*-------------------------------------------------------------------------*)

let rec parseT t = 

    match t with
    | TreeNode ("T", (TreeNode ("not", []))::rest) -> TreeNode ("not", [parseS (List.hd rest)])
    | TreeNode ("T", (TreeNode (str, []))::rest) -> TreeNode (str, [parseS (List.hd rest);
                                                    parseS (List.hd (List.tl rest))])
    | TreeNode (str, _) -> raise (Invalid_argument "Unacceptable input for given grammar.")

and parseS t = 
    match t with
    | TreeNode ("S", (TreeNode ("(", []))::rest) -> parseT (List.hd rest)
    | TreeNode ("S", [TreeNode (str, [])]) -> TreeNode (str, [])
    | TreeNode (str, _) -> raise (Invalid_argument "Unacceptable input for given grammar.")
;;

let buildAbstractSyntaxTree (input : tree) : tree = 

    parseS input
;;  

(*-------------------------------------------------------------------------*)

let satisfiable (input : string list) : (string * bool) list list = 

    let parseTree = buildParseTree input in
    let asTree = buildAbstractSyntaxTree parseTree in
    let vars = scanVariable input in
    let initList = generateInitialAssignList vars

    in
    let rec satisfies assigns acc = 
        match (snd assigns) with
        | true -> acc
        | false -> 
            (
                match (evaluateTree asTree (fst assigns)) with
                | true -> 
                    satisfies (generateNextAssignList (fst assigns)) ((fst assigns)::acc)
                | false ->
                    satisfies (generateNextAssignList (fst assigns)) acc
            )
    in

    List.rev (satisfies (initList, false) [])
;;