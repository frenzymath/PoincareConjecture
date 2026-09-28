import PoincareConjecture.Proofs.M76.Mathlib.CubeShellGeometry
import PoincareConjecture.Proofs.M76.Mathlib.SquareShellSectorTransport











set_option autoImplicit false

open Set Geometry

namespace CubeShell



def coordinatePair (i : Fin 3) (x : Ambient) : ℝ × ℝ := (coordinate i x, ‖x‖)



def lift (f : (ℝ × ℝ) → ℝ × ℝ) (x : Ambient) : Ambient :=
  vector (fun i => (f (coordinatePair i x)).1)



theorem coordinatePair_mem_sector {a b : ℝ} {x : Ambient}
    (hx : x ∈ shell a b) (i : Fin 3) :
    coordinatePair i x ∈ SquareShell.sector a b :=
  ⟨hx, abs_le.mp (abs_coordinate_le_norm x i)⟩




theorem norm_lift {a b c d : ℝ} {f : (ℝ × ℝ) → ℝ × ℝ} {R : ℝ → ℝ}
    (hmap : MapsTo f (SquareShell.sector a b) (SquareShell.sector c d))
    (hrad : ∀ p ∈ SquareShell.sector a b, (f p).2 = R p.2)
    (hedge : ∀ p ∈ SquareShell.sector a b,
      |p.1| = p.2 → |(f p).1| = (f p).2)
    {x : Ambient} (hx : x ∈ shell a b) : ‖lift f x‖ = R ‖x‖ := by
  apply le_antisymm
  · apply (norm_le_iff _ _).mpr
    intro i
    have hp := coordinatePair_mem_sector hx i
    have hi := hmap hp
    change |coordinate i (vector (fun j => (f (coordinatePair j x)).1))| ≤ _
    rw [coordinate_vector]
    have hbound : |(f (coordinatePair i x)).1| ≤ (f (coordinatePair i x)).2 :=
      abs_le.mpr hi.2
    exact hbound.trans_eq (hrad _ hp)
  · obtain ⟨i, hi⟩ := exists_abs_coordinate_eq_norm x
    have hp := coordinatePair_mem_sector hx i
    have he := hedge _ hp hi
    have hcoord : coordinate i (lift f x) = (f (coordinatePair i x)).1 :=
      coordinate_vector _ i
    calc
      R ‖x‖ = (f (coordinatePair i x)).2 := (hrad _ hp).symm
      _ = |(f (coordinatePair i x)).1| := he.symm
      _ = |coordinate i (lift f x)| := congrArg abs hcoord.symm
      _ ≤ ‖lift f x‖ := abs_coordinate_le_norm _ i





theorem coordinatePair_lift {a b c d : ℝ} {f : (ℝ × ℝ) → ℝ × ℝ} {R : ℝ → ℝ}
    (hmap : MapsTo f (SquareShell.sector a b) (SquareShell.sector c d))
    (hrad : ∀ p ∈ SquareShell.sector a b, (f p).2 = R p.2)
    (hedge : ∀ p ∈ SquareShell.sector a b,
      |p.1| = p.2 → |(f p).1| = (f p).2)
    {x : Ambient} (hx : x ∈ shell a b) (i : Fin 3) :
    coordinatePair i (lift f x) = f (coordinatePair i x) := by
  apply Prod.ext
  · exact coordinate_vector _ i
  · exact (norm_lift hmap hrad hedge hx).trans
      (hrad _ (coordinatePair_mem_sector hx i)).symm



theorem lift_mem_shell {a b c d : ℝ} {f : (ℝ × ℝ) → ℝ × ℝ} {R : ℝ → ℝ}
    (hmap : MapsTo f (SquareShell.sector a b) (SquareShell.sector c d))
    (hrad : ∀ p ∈ SquareShell.sector a b, (f p).2 = R p.2)
    (hedge : ∀ p ∈ SquareShell.sector a b,
      |p.1| = p.2 → |(f p).1| = (f p).2)
    {x : Ambient} (hx : x ∈ shell a b) : lift f x ∈ shell c d := by
  have hi := (hmap (coordinatePair_mem_sector hx 0)).1
  change ‖lift f x‖ ∈ Icc c d
  rw [norm_lift hmap hrad hedge hx]
  exact (hrad _ (coordinatePair_mem_sector hx 0)) ▸ hi




theorem lift_leftInvOn {a b c d : ℝ} {f g : (ℝ × ℝ) → ℝ × ℝ} {R : ℝ → ℝ}
    (hmap : MapsTo f (SquareShell.sector a b) (SquareShell.sector c d))
    (hrad : ∀ p ∈ SquareShell.sector a b, (f p).2 = R p.2)
    (hedge : ∀ p ∈ SquareShell.sector a b,
      |p.1| = p.2 → |(f p).1| = (f p).2)
    (hleft : LeftInvOn g f (SquareShell.sector a b)) :
    LeftInvOn (lift g) (lift f) (shell a b) := by
  intro x hx
  have hv : (fun i => (g (coordinatePair i (lift f x))).1) =
      (fun i => coordinate i x) := by
    funext i
    rw [coordinatePair_lift hmap hrad hedge hx]
    exact congrArg Prod.fst (hleft (coordinatePair_mem_sector hx i))
  change vector (fun i => (g (coordinatePair i (lift f x))).1) = x
  rw [hv, vector_coordinate]





theorem finitePiecewiseAffineOn_lift {a b : ℝ} {f : (ℝ × ℝ) → ℝ × ℝ}
    (hf : FinitePiecewiseAffineOn f (SquareShell.sector a b))
    (K : SimplicialComplex ℝ Ambient) (hK : K.faces.Finite)
    (hKs : K.space ⊆ shell a b) : FinitePiecewiseAffineOn (lift f) K.space := by
  have hi (i : Fin 3) :
      FinitePiecewiseAffineOn (fun x => (f (coordinatePair i x)).1) K.space := by
    have hc := (K.affineOnFaces_affine
      (coordinate i).toContinuousAffineMap).finitePiecewiseAffineOn hK
    have hp : FinitePiecewiseAffineOn (coordinatePair i) K.space :=
      hc.prod_mk (finitePiecewiseAffineOn_norm K hK)
    exact (hf.comp hp (fun _ hx => coordinatePair_mem_sector (hKs hx) i)).postcomp
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  exact ((hi 0).prod_mk (hi 1)).prod_mk (hi 2)

end CubeShell
