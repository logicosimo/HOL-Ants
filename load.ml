(* 
./make-checkpoint.sh ~/.local/bin/hol-light-ants \
  "loadt \"/workspaces/hol-light-devcontainer/code/HOL-Ants/setup.ml\""
*)
load_path := "/workspaces/hol-light-devcontainer/code/HOL-Ants" :: !load_path;;
prioritize_num();;
loadt "/workspaces/hol-light-devcontainer/code/HOL-Ants/make.ml";;
loadt "/workspaces/hol-light-devcontainer/code/HOL-Ants/more.ml";;
needs "/workspaces/hol-light-devcontainer/code/HOL-Ants/z3base.ml";;
needs "/workspaces/hol-light-devcontainer/code/HOL-Ants/z3solver.ml";;
needs "/workspaces/hol-light-devcontainer/code/HOL-Ants/z3examples.ml";;
needs "/workspaces/hol-light-devcontainer/code/HOL-Ants/z3ants.ml";;
