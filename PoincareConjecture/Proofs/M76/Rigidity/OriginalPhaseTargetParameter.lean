import PoincareConjecture.Proofs.M76.Rigidity.OriginalPhaseTargetProducts
import PoincareConjecture.Proofs.M76.Rigidity.StandardHierarchyParameterPL
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "E" => ((ℝ × ℝ) × ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates




def hamiltonZeroPhaseParameter (theta : ℝ) (z : E) : X0 :=
  (0, QuotientAddGroup.mk ![z.1.1, z.1.2, theta + z.2])



theorem hamiltonZeroPhaseParameter_eq_product (theta s t u : ℝ) :
    hamiltonZeroPhaseParameter theta ((s, t), u) =
      hamiltonZeroPhaseProduct theta (((s : C0), (t : C0)), u) := by
  apply (Q0).injective
  rw [hamiltonZeroPhaseProduct_coordinates]
  rfl





theorem StandardLatticeHandleAtlas.exists_finite_phase_parameter
    {κ : Type*} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {theta rho : ℝ} (hrho : 0 < rho)
    (hlower : 0 < theta - rho) (hupper : theta + rho < 4 * 16) :
    ∃ K : SimplicialComplex ℝ E,
      K.faces.Finite ∧
      K.space = ((Icc (0 : ℝ) (4 * 16) ×ˢ Icc (0 : ℝ) (4 * 16)) ×ˢ Icc (-rho) rho) ∧
      PolyhedralPLInCharts d (hamiltonZeroPhaseParameter theta) K.space := by
  have hI := isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 4 * 16)
  have hR := isFinitePLBallPair_Icc (show -rho < rho by linarith)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := (hI.prod hI).prod hR
  let a : E →ᴬ[ℝ] E :=
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.prod
      (ContinuousAffineMap.const ℝ E theta +
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap)
  have ha : FinitePiecewiseAffineOn a K.space :=
    (K.affineOnFaces_affine a).finitePiecewiseAffineOn hK
  have hmap : MapsTo a K.space
      ((Icc (0 : ℝ) (4 * 16) ×ˢ Icc (0 : ℝ) (4 * 16)) ×ˢ Icc (0 : ℝ) (4 * 16)) := by
    intro z hz
    have hz' := hKs.subset hz
    change (z.1, theta + z.2) ∈ _
    exact ⟨hz'.1, by linarith [hz'.2.1], by linarith [hz'.2.2]⟩
  have hPL := hd.polyhedralPL_zeroCutParameter.comp_finitePiecewiseAffineOn K hK ha hmap
  change PolyhedralPLInCharts d (hamiltonZeroPhaseParameter theta) K.space at hPL
  exact ⟨K, hK, hKs, hPL⟩

end PoincareConjecture.M76
