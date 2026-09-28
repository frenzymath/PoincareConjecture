import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.RetainedTorus

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
open PeriodicSquare

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "T2" => (AddCircle (64 : ℝ) × AddCircle (64 : ℝ))

theorem PLDomain.exists_original_retained_PL_torus_pair
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    (he : PLDomain e R) (hR : IsCompact R) (S : Bool → Set X0)
    (hS : ∀ b, S b ⊆ frontier R) (x : ∀ b, S b)
    (hcomponent : ∀ b, connectedComponentIn (frontier R) (x b : X0) = S b)
    (hnt : ∀ b, Nontrivial (FundamentalGroup (S b) (x b)))
    (hinj : ∀ b, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S b, X0)) (x b))) :
    ∃ (T : ∀ b, T2 ≃ₜ S b) (v : Bool → ℝ × ℝ → X0),
      (∀ b, PolyhedralPLInCharts e (v b) (squareCarrier 64)) ∧
      (∀ b (z : Square 64), v b (z.1, z.2) = (T b (projection 64 z) : X0)) ∧
      (∀ b, v b '' squareCarrier 64 = S b) := by
  classical
  let : Fact (0 < (64 : ℝ)) := ⟨by norm_num⟩
  have hparam (b : Bool) := he.exists_original_retained_PL_torus hR (hS b)
    (x b) (hcomponent b) (hnt b) (hinj b)
  choose T v hv hvalue using hparam
  refine ⟨T, v, hv, hvalue, ?_⟩
  intro b
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    let z' : Square 64 := (⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩)
    exact (hvalue b z').symm ▸ (T b (projection 64 z')).property
  · intro hy
    obtain ⟨z, hz⟩ := surjective_projection (64 : ℝ) ((T b).symm ⟨y, hy⟩)
    refine ⟨(z.1, z.2), ⟨z.1.property, z.2.property⟩, ?_⟩
    rw [hvalue, hz, (T b).apply_symm_apply]

end PoincareConjecture.M76
