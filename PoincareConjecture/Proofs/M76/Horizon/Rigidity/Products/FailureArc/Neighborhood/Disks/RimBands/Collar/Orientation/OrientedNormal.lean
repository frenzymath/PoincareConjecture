import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Charts.TangentialCharts
import PoincareConjecture.Proofs.M76.Brown.NormalBundleCore








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_normal_units_of_orientation_labels
    {X ι : Type*} [TopologicalSpace X] {S : Set X}
    (A : BrownCollar.FlatteningAtlas P2 S ι)
    (hPL : ∀ i j, A.transition i j ∈ piecewiseAffineGroupoid C3)
    (ambient tangent : ∀ i, LocallyConstant (A.baseSet i) SignTypeˣ)
    (hamb : ∀ i j (x : S) (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j),
      (ambient j ⟨x, hj⟩ : SignType) =
        plLocalSign (A.transition i j) (hPL i j)
          ⟨(A.coordinate i x, 0), A.transition_mem_source i j x ⟨hi, hj⟩⟩ *
            (ambient i ⟨x, hi⟩ : SignType))
    (htan : ∀ i j (x : S) (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j),
      (tangent j ⟨x, hj⟩ : SignType) =
        plLocalSign (atlasTangentialTransition A i j)
          (tangentialTransition_mem_piecewiseAffineGroupoid _ (hPL i j) _)
          ⟨A.coordinate i x, A.transition_mem_source i j x ⟨hi, hj⟩⟩ *
            (tangent i ⟨x, hi⟩ : SignType)) :
    ∃ a : ι → S → SignTypeˣ,
      (∀ i, ContinuousOn (a i) (A.baseSet i)) ∧
      (∀ i (x : A.baseSet i), a i x = ambient i x * tangent i x) ∧
      ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
        a j x = A.transitionUnit i j x * a i x := by
  classical
  let a (i : ι) (x : S) : SignTypeˣ :=
    if hx : x ∈ A.baseSet i then ambient i ⟨x, hx⟩ * tangent i ⟨x, hx⟩ else 1
  have ha (i : ι) (x : A.baseSet i) :
      a i x = ambient i x * tangent i x := dif_pos x.property
  refine ⟨a, ?_, ha, ?_⟩
  · intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (A.baseSet i).domRestrict (a i) =
        fun x => ambient i x * tangent i x := funext (ha i)
    rw [he]
    exact (ambient i).continuous.mul (tangent i).continuous
  · intro i j x hx
    rw [show a i x = ambient i ⟨x, hx.1⟩ * tangent i ⟨x, hx.1⟩ from ha i ⟨x, hx.1⟩,
      show a j x = ambient j ⟨x, hx.2⟩ * tangent j ⟨x, hx.2⟩ from ha j ⟨x, hx.2⟩]
    apply Units.ext
    simp only [Units.val_mul, BrownCollar.FlatteningAtlas.transitionUnit, Units.val_mk0]
    rw [hamb i j x hx.1 hx.2, htan i j x hx.1 hx.2,
      atlasTransition_sign_factorization A i j (hPL i j) x hx]
    have hn := plLocalSign_ne_zero (atlasTangentialTransition A i j)
      (tangentialTransition_mem_piecewiseAffineGroupoid _ (hPL i j) _)
      ⟨A.coordinate i x, A.transition_mem_source i j x hx⟩
    have hs :
        plLocalSign (atlasTangentialTransition A i j)
          (tangentialTransition_mem_piecewiseAffineGroupoid _ (hPL i j) _)
          ⟨A.coordinate i x, A.transition_mem_source i j x hx⟩ *
        plLocalSign (atlasTangentialTransition A i j)
          (tangentialTransition_mem_piecewiseAffineGroupoid _ (hPL i j) _)
          ⟨A.coordinate i x, A.transition_mem_source i j x hx⟩ = 1 :=
      mul_inv_cancel₀ hn
    calc
      _ = (plLocalSign (atlasTangentialTransition A i j)
          (tangentialTransition_mem_piecewiseAffineGroupoid _ (hPL i j) _)
          ⟨A.coordinate i x, A.transition_mem_source i j x hx⟩ *
        plLocalSign (atlasTangentialTransition A i j)
          (tangentialTransition_mem_piecewiseAffineGroupoid _ (hPL i j) _)
          ⟨A.coordinate i x, A.transition_mem_source i j x hx⟩) *
        (A.transitionSign i j x *
          ((ambient i ⟨x, hx.1⟩ : SignType) * (tangent i ⟨x, hx.1⟩ : SignType))) := by
            ac_rfl
      _ = _ := by rw [hs, one_mul]

end PoincareConjecture.M76.Dehn.Annuli.RimBands
