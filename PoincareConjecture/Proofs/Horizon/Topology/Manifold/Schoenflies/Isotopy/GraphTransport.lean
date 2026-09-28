import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Flow
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

theorem exists_supported_graph_transport_within_preserving_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (a h : E → Real) (ha : ContDiff Real ∞ a) (hh : ContDiff Real ∞ h)
    {K : Set E} (hK : IsCompact K) {U : Set (E × Real)} (hU : IsOpen U)
    (htrace : ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ K, (x, a x + t * h x) ∈ U) :
    ∃ S : Set (E × Real), IsCompact S ∧ S ⊆ U ∧
      ∃ F : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ y ∉ S, F y = y) ∧
        (∀ y, (F y).1 = y.1) ∧
        (∀ x z, h x = 0 → F (x, z) = (x, z)) ∧
        ∀ x ∈ K, F (x, a x) = (x, a x + h x) := by
  let q : Real × E → E × Real := fun z => (z.2, a z.2 + z.1 * h z.2)
  have hq : Continuous q := continuous_snd.prodMk
    ((ha.continuous.comp continuous_snd).add
      (continuous_fst.mul (hh.continuous.comp continuous_snd)))
  let T := q '' (Icc (0 : Real) 1 ×ˢ K)
  have hT : IsCompact T := (isCompact_Icc.prod hK).image hq
  have hTU : T ⊆ U := by
    rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact htrace t ht x hx
  obtain ⟨χ, hχ, hχc, hχU, hχT⟩ :=
    Poincare.Parabolic.Interior.exists_contDiff_compact_cutoff hT hU hTU
  let V : E × Real → E × Real := fun y => χ y • (0, h y.1)
  have hV : ContDiff Real ∞ V := hχ.smul
    (contDiff_const.prodMk (hh.comp contDiff_fst))
  have hVc : HasCompactSupport V := hχc.smul_right
  obtain ⟨Phi, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support
      (fun z : Real × (E × Real) => V z.2) (hV.comp contDiff_snd)
      hχc.isCompact (fun _ y hy => by
        change χ y • (0, h y.1) = 0
        rw [image_eq_zero_of_notMem_tsupport hy, zero_smul])
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hV (by simp)
  have hfirst (y : E × Real) : (Phi 0 1 y).1 = y.1 := by
    have hd (t : Real) : HasDerivAt (fun t => (Phi 0 t y).1) 0 t := by
      have hd := (ContinuousLinearMap.fst Real E Real).hasFDerivAt.comp_hasDerivAt t (ho 0 y t)
      change HasDerivAt (fun t => (Phi 0 t y).1) (χ (Phi 0 t y) • (0 : E)) t at hd
      simpa only [smul_zero] using hd
    have he := is_const_of_deriv_eq_zero
      (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
    simpa only [hi] using he
  have hstationary (y : E × Real) (hy : h y.1 = 0) : Phi 0 1 y = y := by
    have hVy : V y = 0 := by simp [V, hy]
    have heq := ODE_solution_unique (a := 0) (b := 1) (v := fun _ => V) (fun _ => hL)
      (f := fun t => Phi 0 t y) (g := fun _ => y)
      ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun t _ => (ho 0 y t).hasDerivWithinAt)
      continuous_const.continuousOn
      (fun t _ => by rw [hVy]; exact (hasDerivAt_const t y).hasDerivWithinAt)
      (hi 0 y)
    exact heq (by simp)
  refine ⟨tsupport χ, hχc.isCompact, hχU, Phi 0 1, hfix 0 1, hfirst,
    fun x z hx => hstationary (x, z) hx, ?_⟩
  intro x hx
  have hvel (t : Real) (ht : t ∈ Icc (0 : Real) 1) : V (q (t, x)) = (0, h x) := by
    have hmem : q (t, x) ∈ T := mem_image_of_mem q ⟨ht, hx⟩
    change χ (q (t, x)) • (0, h x) = (0, h x)
    rw [(hχT _ hmem).eq_of_nhds, one_smul]
  have hder (t : Real) : HasDerivAt (fun t => q (t, x)) (0, h x) t := by
    simpa [q] using (hasDerivAt_const t x).prodMk
      ((hasDerivAt_const t (a x)).add ((hasDerivAt_id t).mul_const (h x)))
  have heq := ODE_solution_unique (v := fun _ => V) (fun _ => hL)
    (f := fun t => Phi 0 t (x, a x)) (g := fun t => q (t, x))
    ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun t _ => (ho 0 (x, a x) t).hasDerivWithinAt)
    (hq.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun t ht => by rw [hvel t (Ico_subset_Icc_self ht)]; exact (hder t).hasDerivWithinAt)
    (by simp [hi, q])
  simpa [q] using heq (show (1 : Real) ∈ Icc 0 1 by simp)

theorem exists_supported_graph_transport_within
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (a h : E → Real) (ha : ContDiff Real ∞ a) (hh : ContDiff Real ∞ h)
    {K : Set E} (hK : IsCompact K) {U : Set (E × Real)} (hU : IsOpen U)
    (htrace : ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ K, (x, a x + t * h x) ∈ U) :
    ∃ S : Set (E × Real), IsCompact S ∧ S ⊆ U ∧
      ∃ F : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ y ∉ S, F y = y) ∧
        (∀ x z, h x = 0 → F (x, z) = (x, z)) ∧
        ∀ x ∈ K, F (x, a x) = (x, a x + h x) := by
  obtain ⟨S, hS, hSU, F, hfix, _, hzero, hmap⟩ :=
    exists_supported_graph_transport_within_preserving_base a h ha hh hK hU htrace
  exact ⟨S, hS, hSU, F, hfix, hzero, hmap⟩

theorem exists_supported_local_graph_flattening_preserving_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (a : E → Real) {V : Set E} (hV : IsOpen V) (ha : ContDiffOn Real ∞ a V)
    {K : Set E} (hK : IsCompact K) (hKV : K ⊆ V)
    {U : Set (E × Real)} (hU : IsOpen U)
    (htrace : ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ K, (x, (1 - t) * a x) ∈ U) :
    ∃ S : Set (E × Real), IsCompact S ∧ S ⊆ U ∧
      ∃ F : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ y ∉ S, F y = y) ∧
        (∀ y, (F y).1 = y.1) ∧
        (∀ x z, a x = 0 → F (x, z) = (x, z)) ∧
        ∀ x ∈ K, F (x, a x) = (x, 0) := by
  obtain ⟨χ, hχ, _, hχV, hχK⟩ :=
    Poincare.Parabolic.Interior.exists_contDiff_compact_cutoff hK hV hKV
  let b : E → Real := fun x => χ x • a x
  have hb : ContDiff Real ∞ b :=
    Poincare.Parabolic.Interior.contDiff_smul_cutoff hV ha hχ hχV
  have hbK (x : E) (hx : x ∈ K) : b x = a x := by
    simp [b, (hχK x hx).eq_of_nhds]
  obtain ⟨S, hS, hSU, F, hfix, hfirst, hzero, hmap⟩ :=
    exists_supported_graph_transport_within_preserving_base b (fun x => -b x) hb hb.neg hK hU
      (fun t ht x hx => by
        rw [hbK x hx]
        convert htrace t ht x hx using 1
        congr 1
        ring)
  refine ⟨S, hS, hSU, F, hfix, hfirst, ?_, ?_⟩
  · intro x z hx
    exact hzero x z (by simp [b, hx])
  · intro x hx
    simpa only [hbK x hx, add_neg_cancel] using hmap x hx

theorem exists_supported_local_graph_flattening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (a : E → Real) {V : Set E} (hV : IsOpen V) (ha : ContDiffOn Real ∞ a V)
    {K : Set E} (hK : IsCompact K) (hKV : K ⊆ V)
    {U : Set (E × Real)} (hU : IsOpen U)
    (htrace : ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ K, (x, (1 - t) * a x) ∈ U) :
    ∃ S : Set (E × Real), IsCompact S ∧ S ⊆ U ∧
      ∃ F : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ y ∉ S, F y = y) ∧
        (∀ x z, a x = 0 → F (x, z) = (x, z)) ∧
        ∀ x ∈ K, F (x, a x) = (x, 0) := by
  obtain ⟨S, hS, hSU, F, hfix, _, hzero, hmap⟩ :=
    exists_supported_local_graph_flattening_preserving_base a hV ha hK hKV hU htrace
  exact ⟨S, hS, hSU, F, hfix, hzero, hmap⟩

end Poincare.Manifold.Schoenflies
