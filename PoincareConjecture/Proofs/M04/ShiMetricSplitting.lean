import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_point_splitting_metric_edist [T2Space M]
    (g : RiemannianMetric n M) (p q : M) {r ell a : ℝ}
    (hell : 0 ≤ ell) (hellr : ell < r)
    (hcompact : IsCompact (closure (g.ball p r)))
    (hpq : g.edist p q = ENNReal.ofReal ell)
    (ha : 0 ≤ a) (haell : a ≤ ell) :
    ∃ z ∈ g.ball p r,
      g.edist p z = ENNReal.ofReal a ∧
      g.edist z q = ENNReal.ofReal (ell - a) := by
  let hrpos : 0 < r := lt_of_le_of_lt hell hellr

  have hed_self (x : M) : g.edist x x = 0 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 n) x x = 0
    exact Manifold.riemannianEDist_self

  have hed_triangle (x y z : M) :
      g.edist x z ≤ g.edist x y + g.edist y z := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 n) x z ≤
      Manifold.riemannianEDist (𝓡 n) x y + Manifold.riemannianEDist (𝓡 n) y z
    exact Manifold.riemannianEDist_triangle

  have hed_le_path {γ : ℝ → M} {b c : ℝ}
      (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc b c)) (hbc : b ≤ c) :
      g.edist (γ b) (γ c) ≤ g.pathELength γ b c := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 n) (γ b) (γ c) ≤
      Manifold.pathELength (𝓡 n) γ b c
    exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hbc

  have hpath_add {γ : ℝ → M} {b c d : ℝ} (hbc : b ≤ c) (hcd : c ≤ d) :
      g.pathELength γ b c + g.pathELength γ c d = g.pathELength γ b d := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.pathELength (𝓡 n) γ b c +
      Manifold.pathELength (𝓡 n) γ c d = Manifold.pathELength (𝓡 n) γ b d
    exact Manifold.pathELength_add hbc hcd

  have hexists_path {x y : M} {L : ℝ≥0∞} (hxy : g.edist x y < L) :
      ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ ∧ g.pathELength γ 0 1 < L := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    obtain ⟨γ, h0, h1, hγ, hL, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hxy zero_lt_one
    exact ⟨γ, h0, h1, hγ, hL⟩

  have hcont : Continuous (fun x : M => g.edist p x) := by
    let : LocallyCompactSpace M :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
    let : PseudoEMetricSpace M := .ofRiemannianMetric (𝓡 n) M
    exact continuous_const.edist continuous_id

  have hcont_q : Continuous (fun x : M => g.edist x q) := by
    let : LocallyCompactSpace M :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
    let : PseudoEMetricSpace M := .ofRiemannianMetric (𝓡 n) M
    exact continuous_id.edist continuous_const

  have hpball : p ∈ g.ball p r := by
    change g.edist p p < ENNReal.ofReal r
    rw [hed_self]
    exact (ENNReal.ofReal_pos.2 hrpos)

  rcases eq_or_lt_of_le haell with rfl | haell'
  · refine ⟨q, ?_, ?_, ?_⟩
    · change g.edist p q < ENNReal.ofReal r
      rw [hpq]
      exact ENNReal.ofReal_lt_ofReal_iff hrpos |>.2 hellr
    · exact hpq
    · rw [sub_self, ENNReal.ofReal_zero, hed_self]
  rcases eq_or_lt_of_le ha with rfl | hapos
  · refine ⟨p, hpball, ?_, ?_⟩
    · simpa using hed_self p
    · simpa [sub_zero] using hpq
  have hart : a < r := lt_of_le_of_lt haell hellr
  let S : Set M := {z | g.edist p z = ENNReal.ofReal a}
  have hSclosed : IsClosed S := by
    exact isClosed_eq hcont continuous_const
  have hSsub : S ⊆ closure (g.ball p r) := by
    intro z hz
    apply subset_closure
    change g.edist p z < ENNReal.ofReal r
    rw [hz]
    exact ENNReal.ofReal_lt_ofReal_iff hrpos |>.2 hart
  have hScompact : IsCompact S := hcompact.of_isClosed_subset hSclosed hSsub

  have hSnonempty : S.Nonempty := by
    have hlt : g.edist p q < ENNReal.ofReal (ell + 1) := by
      rw [hpq]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    obtain ⟨γ, hγ0, hγ1, hγ, hγL⟩ :=
      hexists_path (L := ENNReal.ofReal (ell + 1)) hlt
    have hIV : ENNReal.ofReal a ∈
        Icc (g.edist p (γ 0)) (g.edist p (γ 1)) := by
      rw [hγ0, hγ1, hed_self, hpq]
      exact ⟨bot_le, ENNReal.ofReal_le_ofReal haell⟩
    obtain ⟨u, hu, huS⟩ :=
      intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1)
        (hcont.comp hγ.continuous).continuousOn hIV
    exact ⟨γ u, huS⟩

  obtain ⟨z, hzS, hzmin⟩ :=
    hScompact.exists_isMinOn hSnonempty
      hcont_q.continuousOn

  have hdist_eps (ε : ℝ≥0∞) (hε : 0 < ε) :
      g.edist z q ≤ ENNReal.ofReal (ell - a) + ε := by
    have hlt : g.edist p q < g.edist p q + ε := by
      rw [hpq]
      exact ENNReal.lt_add_right ENNReal.ofReal_ne_top hε.ne'
    obtain ⟨γ, hγ0, hγ1, hγ, hγL⟩ := hexists_path hlt
    have hIV : ENNReal.ofReal a ∈
        Icc (g.edist p (γ 0)) (g.edist p (γ 1)) := by
      rw [hγ0, hγ1, hed_self, hpq]
      exact ⟨bot_le, ENNReal.ofReal_le_ofReal haell⟩
    obtain ⟨u, hu, huS⟩ :=
      intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1)
        (hcont.comp hγ.continuous).continuousOn hIV
    have huS' : g.edist p (γ u) = ENNReal.ofReal a := by
      simpa [Function.comp_def] using huS
    have hu_mem : γ u ∈ S := huS'
    have hzle : g.edist z q ≤ g.edist (γ u) q := hzmin hu_mem
    have hleft : ENNReal.ofReal a ≤ g.pathELength γ 0 u := by
      rw [← huS']
      rw [← hγ0]
      exact hed_le_path hγ.contMDiffOn hu.1
    have hright : g.edist (γ u) q ≤ g.pathELength γ u 1 := by
      simpa [hγ1] using hed_le_path hγ.contMDiffOn hu.2
    have hsum : ENNReal.ofReal a + g.edist z q ≤
        g.pathELength γ 0 1 := by
      calc
        _ ≤ g.pathELength γ 0 u + g.pathELength γ u 1 :=
          add_le_add hleft (hzle.trans hright)
        _ = g.pathELength γ 0 1 := hpath_add hu.1 hu.2
    have hsum' : ENNReal.ofReal a + g.edist z q ≤
        g.edist p q + ε := hsum.trans hγL.le
    have hA : ENNReal.ofReal a ≤ g.edist p q + ε := by
      rw [hpq]
      exact (ENNReal.ofReal_le_ofReal haell).trans
        (le_add_of_nonneg_right bot_le)
    have hsub : g.edist z q ≤
        (g.edist p q + ε) - ENNReal.ofReal a :=
      (ENNReal.le_sub_iff_add_le_left ENNReal.ofReal_ne_top hA).2 hsum'
    rw [hpq, ← ENNReal.sub_add_eq_add_sub
      (ENNReal.ofReal_le_ofReal haell) ENNReal.ofReal_ne_top,
      ← ENNReal.ofReal_sub ell ha] at hsub
    exact hsub

  have hdist : g.edist z q ≤ ENNReal.ofReal (ell - a) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    exact hdist_eps (ε : ℝ≥0∞) (ENNReal.coe_pos.mpr hε)

  have hreverse : ENNReal.ofReal (ell - a) ≤ g.edist z q := by
    have htri := hed_triangle p z q
    rw [hzS, hpq] at htri
    have hsumle : ENNReal.ofReal a + ENNReal.ofReal (ell - a) ≤
        ENNReal.ofReal a + g.edist z q := by
      have hadd : ENNReal.ofReal a + ENNReal.ofReal (ell - a) =
          ENNReal.ofReal ell := by
        rw [← ENNReal.ofReal_add ha (sub_nonneg.mpr haell)]
        congr 1
        linarith
      rw [hadd]
      exact htri
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp hsumle
  refine ⟨z, ?_, hzS, le_antisymm hdist hreverse⟩
  change g.edist p z < ENNReal.ofReal r
  rw [hzS]
  exact ENNReal.ofReal_lt_ofReal_iff hrpos |>.2 hart

end PoincareConjecture.M04
