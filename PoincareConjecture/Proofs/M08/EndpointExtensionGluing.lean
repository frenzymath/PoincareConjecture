import PoincareConjecture.Proofs.M08.EndpointEulerEquation
import PoincareConjecture.Proofs.M08.GlobalCurveExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def restrictParametricVelocityExtension {C U : Set ℝ} (hU : IsOpen U)
    (hCU : C ⊆ U) (hC : UniqueDiffOn ℝ C) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (E : ParametricAlongCurveExtensionOn U α (curveVelocityWithin (n := n) α U)) :
    ParametricAlongCurveExtensionOn C α (curveVelocityWithin (n := n) α C) where
  extension := E.extension
  domain := E.domain
  open_domain := E.open_domain
  graph_mem s hs := E.graph_mem s (hCU hs)
  smooth := E.smooth
  agrees s hs := (E.agrees s (hCU hs)).trans
    (curveVelocityWithin_eq_of_uniqueDiff hU hCU hC α hα hs).symm

theorem restrictParametricVelocityExtension_equation {J C U : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (hU : IsOpen U)
    (hCU : C ⊆ U) (hC : UniqueDiffOn ℝ C) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (E : ParametricAlongCurveExtensionOn U α (curveVelocityWithin (n := n) α U))
    {s : ℝ} (hs : s ∈ C) (heq : regularizedLGeodesicEquation F T α U E s) :
    regularizedLGeodesicEquation F T α C
      (restrictParametricVelocityExtension hU hCU hC α hα E) s := by
  intro W
  unfold regularizedEulerResidual pullbackCovariantDerivative restrictParametricVelocityExtension
  rw [curveVelocityWithin_eq_of_uniqueDiff hU hCU hC α hα hs]
  exact heq W

theorem exists_local_velocityExtension_of_smooth {U : Set ℝ} (hU : IsOpen U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U) {s : ℝ} (hs : s ∈ U) :
    ∃ V : Set ℝ, IsOpen V ∧ s ∈ V ∧ V ⊆ U ∧
      Nonempty (ParametricAlongCurveExtensionOn V α (curveVelocityWithin (n := n) α V)) := by
  let x := α s
  let V := U ∩ α ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  have hV : IsOpen V := hα.continuousOn.isOpen_inter_preimage hU
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  exact ⟨V, hV, ⟨hs, mem_chart_source _ _⟩, inter_subset_left,
    ⟨chartVelocityExtension hV x α (hα.mono inter_subset_left) (fun _ hr ↦ hr.2)⟩⟩

variable {ι : Type v}

theorem gluedParametricExtension_equation_at {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (U : ι → Set ℝ) (hU : ∀ i, IsOpen (U i)) (α : ℝ → M)
    (E : ∀ i, ParametricAlongCurveExtensionOn (U i) α
      (curveVelocityWithin (n := n) α (U i)))
    (hρ : ρ.IsSubordinate (fun i ↦ (Subtype.val : I → ℝ) ⁻¹' U i))
    (s : I) (heq : ∀ i ∈ ρ.fintsupport s,
      regularizedLGeodesicEquation F T α (U i) (E i) s) :
    regularizedLGeodesicEquation F T α I
      (gluedParametricExtension I ρ U hU α E hρ) s := by
  intro W
  let G := (F.metric (T - (s : ℝ) ^ 2)).inner (α s)
  let V (i : ι) := pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
    (curveVelocityWithin (n := n) α (U i)) (U i) (E i) s
  let R := scalarCurvatureDifferential F (fun r ↦ T - r ^ 2) α s W
  let C := 4 * (s : ℝ) * (F.connection (T - (s : ℝ) ^ 2)).ricci (α s)
    (curveVelocityWithin (n := n) α I s) W
  let B := 2 * (s : ℝ) ^ 2 * R - C
  have hS := (timePartitionWeight_eventually_support_subset I ρ s).self_of_nhds
  have hinnerLocal : ∀ i ∈ ρ.fintsupport s, G (V i) W = B := by
    intro i hi
    have hsU : (s : ℝ) ∈ U i := hρ i ((ρ.mem_fintsupport_iff s i).mp hi)
    have h := heq i hi W
    unfold regularizedEulerResidual at h
    rw [← curveVelocityWithin_eq_of_open I.isOpen (hU i) s.property hsU] at h
    change G (V i) W - 2 * (s : ℝ) ^ 2 * R + C = 0 at h
    dsimp only [B]
    linarith
  have hmetric : G (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) • V i) W =
      ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) * G (V i) W := by
    rw [map_sum]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [G.map_smul]
    rfl
  have hinner : G (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
      (curveVelocityWithin (n := n) α I) I
      (gluedParametricExtension I ρ U hU α E hρ) s) W = B := by
    rw [gluedParametricExtension_pullback F (fun r ↦ T - r ^ 2) I ρ U hU α E hρ s]
    change G (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) • V i) W = B
    rw [hmetric]
    calc
      (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) * G (V i) W) =
          ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ) * B :=
        Finset.sum_congr rfl (fun i hi ↦ congrArg
          (fun r ↦ timePartitionWeight I ρ i (s : ℝ) * r) (hinnerLocal i hi))
      _ = (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i (s : ℝ)) * B :=
        (Finset.sum_mul ..).symm
      _ = B := by rw [timePartitionWeight_sum_eq_one I ρ s hS, one_mul]
  change G (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
      (curveVelocityWithin (n := n) α I) I
      (gluedParametricExtension I ρ U hU α E hρ) s) W - 2 * (s : ℝ) ^ 2 * R + C = 0
  rw [hinner]
  dsimp only [B]
  ring

theorem exists_closedEuler_extension_of_local {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {C U : Set ℝ} (hCclosed : IsClosed C) (hC : UniqueDiffOn ℝ C)
    (hU : IsOpen U) (hCU : C ⊆ U) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hloc : ∀ s ∈ C, ∃ V : Set ℝ, IsOpen V ∧ s ∈ V ∧ V ⊆ U ∧
      ∃ E : ParametricAlongCurveExtensionOn V α (curveVelocityWithin (n := n) α V),
        ∀ r ∈ V, r ∈ C → regularizedLGeodesicEquation F T α V E r) :
    ∃ E : ParametricAlongCurveExtensionOn C α (curveVelocityWithin (n := n) α C),
      ∀ s ∈ C, regularizedLGeodesicEquation F T α C E s := by
  classical
  have hlocal (s : ℝ) (hs : s ∈ U) :
      ∃ V : Set ℝ, IsOpen V ∧ s ∈ V ∧ V ⊆ U ∧
        ∃ E : ParametricAlongCurveExtensionOn V α (curveVelocityWithin (n := n) α V),
          ∀ r ∈ V, r ∈ C → regularizedLGeodesicEquation F T α V E r := by
    by_cases hsC : s ∈ C
    · exact hloc s hsC
    · obtain ⟨V, hV, hsV, hVU, ⟨E⟩⟩ := exists_local_velocityExtension_of_smooth
        (hU.sdiff hCclosed) α (hα.mono sdiff_subset) ⟨hs, hsC⟩
      exact ⟨V, hV, hsV, hVU.trans sdiff_subset, E,
        fun r hr hrC ↦ False.elim ((hVU hr).2 hrC)⟩
  let O : TopologicalSpace.Opens ℝ := ⟨U, hU⟩
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  choose V hV hsV _hsub E heq using fun s : O ↦ hlocal s s.property
  have hcover : (univ : Set O) ⊆ ⋃ i : O, (Subtype.val : O → ℝ) ⁻¹' V i := by
    intro s _
    exact mem_iUnion.mpr ⟨s, hsV s⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SmoothPartitionOfUnity O (𝓘(ℝ, ℝ)) O univ,
      ρ.IsSubordinate (fun i ↦ (Subtype.val : O → ℝ) ⁻¹' V i) :=
    SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ)) isClosed_univ _
      (fun i ↦ (hV i).preimage continuous_subtype_val) hcover
  let Eg := gluedParametricExtension O ρ V hV α E hρ
  refine ⟨restrictParametricVelocityExtension hU hCU hC α hα Eg, ?_⟩
  intro s hs
  apply restrictParametricVelocityExtension_equation F T hU hCU hC α hα Eg hs
  apply gluedParametricExtension_equation_at F T O ρ V hV α E hρ ⟨s, hCU hs⟩
  intro i hi
  exact heq i s (hρ i ((ρ.mem_fintsupport_iff ⟨s, hCU hs⟩ i).mp hi)) hs

end PoincareConjecture.M08

