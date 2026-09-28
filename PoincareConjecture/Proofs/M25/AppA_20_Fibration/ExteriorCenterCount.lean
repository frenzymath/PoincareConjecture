import PoincareConjecture.Proofs.M25.AppA_1_Necks.SharpDepth
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Overlap_A11
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

theorem NeckOnlyCover.exists_exterior_center_count_bound :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      ∀ (K : Set M), IsCompact K → K ⊆ H.X →
      ∃ B : ℕ, ∀ (m : ℕ) (N : Fin m → EpsilonNeck g),
        (∀ i, (N i).epsilon = H.epsilon) →
        (∀ i, (N i).center ∈ K) →
        (∀ i j, i < j → (N j).center ∉ (N i).carrier) →
        m ≤ B := by
  obtain ⟨epsilon0, hpos, hcap, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := (1 / 2 : ℝ)) (by norm_num)
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g H hsmall K hK hKX
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  by_cases hKempty : K = ∅
  · refine ⟨0, ?_⟩
    intro m N _hepsilon hcenters _hhistory
    cases m with
    | zero => exact le_rfl
    | succ m =>
      have hx := hcenters (0 : Fin (m + 1))
      rw [hKempty] at hx
      exact False.elim hx
  have hcover : K ⊆ ⋃ R ∈ H.necks, R.carrier := by
    intro x hx
    obtain ⟨R, hR, hcenter⟩ := H.pointwise_center_cover x (hKX hx)
    refine mem_iUnion₂.mpr ⟨R, hR, ?_⟩
    rw [← hcenter]
    exact R.central_sphere_subset R.center_on_central_sphere
  obtain ⟨F, hFsub, hFfinite, hFcover⟩ :=
    hK.elim_finite_subcover_image
      (b := H.necks) (c := fun R : EpsilonNeck g => R.carrier)
      (fun R _ => R.carrier_open) hcover
  have hFnonempty : F.Nonempty := by
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hKempty
    obtain ⟨R, hR, _⟩ := mem_iUnion₂.mp (hFcover hx)
    exact ⟨R, hR⟩
  obtain ⟨R0, _, hminimum⟩ :=
    Set.exists_min_image F (fun R : EpsilonNeck g => R.scale) hFfinite hFnonempty
  let r : ℝ := R0.scale / 2
  have hr : 0 < r := half_pos R0.scale_pos
  have hlower (N : EpsilonNeck g) (hepsilon : N.epsilon = H.epsilon)
      (hcenter : N.center ∈ K) : r < N.scale := by
    obtain ⟨R, hR, hRN⟩ := mem_iUnion₂.mp (hFcover hcenter)
    have hRsmall : R.epsilon ≤ epsilon0 := by
      rw [H.neck_epsilon R (hFsub hR)]
      exact hsmall
    have hNsmall : N.epsilon ≤ epsilon0 := by
      rw [hepsilon]
      exact hsmall
    have hinter : (R.carrier ∩ N.carrier).Nonempty :=
      ⟨N.center, hRN, N.central_sphere_subset N.center_on_central_sphere⟩
    have hratio := (hscale R N hRsmall hNsmall hinter).2
    have hhalf : (1 / 2 : ℝ) < N.scale / R.scale := by
      linarith [(abs_lt.mp hratio).1]
    have hproduct := (lt_div_iff₀ R.scale_pos).mp hhalf
    have hminR : R0.scale ≤ R.scale := hminimum R hR
    dsimp only [r]
    linarith
  let L : ℝ := H.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr H.epsilon_pos
  have hHepsilon : H.epsilon ≤ 1 / 200 := hsmall.trans hcap
  have hsqrt : 0 < Real.sqrt (1 - H.epsilon) :=
    Real.sqrt_pos.mpr (by linarith)
  let d : ℝ := r * Real.sqrt (1 - H.epsilon) * L
  have hd : 0 < d := mul_pos (mul_pos hr hsqrt) hL
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hradius : 0 < ENNReal.ofReal (d / 3) :=
    ENNReal.ofReal_pos.mpr (div_pos hd (by norm_num))
  obtain ⟨T, hTfinite, hTcover⟩ :=
    EMetric.totallyBounded_iff.mp hK.totallyBounded (ENNReal.ofReal (d / 3)) hradius
  let : Fintype T := hTfinite.fintype
  refine ⟨Fintype.card T, ?_⟩
  intro m N hepsilon hcenters hhistory
  have hseparation_lt (i j : Fin m) (hij : i < j) :
      ENNReal.ofReal d ≤ edist (N i).center (N j).center := by
    have hc := ((N i).mem_central_sphere_iff (N i).center).mp
      (N i).center_on_central_sphere
    have hdepthi : (N i).axialDepth (N i).center = L := by
      simp only [EpsilonNeck.axialDepth, if_pos hc.1, hc.2, abs_zero, sub_zero,
        hepsilon i, L]
    have hdepthj : (N i).axialDepth (N j).center = 0 := by
      simp only [EpsilonNeck.axialDepth, if_neg (hhistory i j hij)]
    have hdepth := (N i).axialDepth_edist_le (N i).center (N j).center
    rw [hdepthi, hdepthj, sub_zero, abs_of_pos hL, hepsilon i] at hdepth
    have hreal : d ≤ (N i).scale * Real.sqrt (1 - H.epsilon) * L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hlower (N i) (hepsilon i) (hcenters i)).le hsqrt.le)
        hL.le
    change ENNReal.ofReal d ≤ g.edist (N i).center (N j).center
    exact (ENNReal.ofReal_le_ofReal hreal).trans hdepth
  have hseparation (i j : Fin m) (hij : i ≠ j) :
      ENNReal.ofReal d ≤ edist (N i).center (N j).center := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hseparation_lt i j hlt
    · simpa only [edist_comm] using hseparation_lt j i hgt
  have hball (i : Fin m) :
      ∃ y : T, edist (N i).center (y : M) < ENNReal.ofReal (d / 3) := by
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hTcover (hcenters i))
    exact ⟨⟨y, hy⟩, Metric.mem_eball.mp hxy⟩
  let p : Fin m → T := fun i => Classical.choose (hball i)
  have hp (i : Fin m) : edist (N i).center (p i : M) < ENNReal.ofReal (d / 3) :=
    Classical.choose_spec (hball i)
  have hinjective : Function.Injective p := by
    intro i j hpij
    by_contra hij
    have hpj : edist (N j).center (p i : M) < ENNReal.ofReal (d / 3) := by
      rw [hpij]
      exact hp j
    have hshort : edist (N i).center (N j).center < ENNReal.ofReal d := by
      calc
        _ ≤ edist (N i).center (p i : M) + edist (N j).center (p i : M) :=
          edist_triangle_right _ _ _
        _ < ENNReal.ofReal (d / 3) + ENNReal.ofReal (d / 3) :=
          ENNReal.add_lt_add (hp i) hpj
        _ = ENNReal.ofReal (d / 3 + d / 3) :=
          (ENNReal.ofReal_add (div_nonneg hd.le (by norm_num))
            (div_nonneg hd.le (by norm_num))).symm
        _ < ENNReal.ofReal d := (ENNReal.ofReal_lt_ofReal_iff hd).mpr (by linarith)
    exact (not_lt_of_ge (hseparation i j hij)) hshort
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective p hinjective

end PoincareConjecture
