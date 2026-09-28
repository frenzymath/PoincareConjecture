import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Set Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem exists_smooth_endpoint_family (γ : ℝ → M) (D : Set ℝ)
    (hD : IsOpen D) (hI : Set.Icc (0 : ℝ) 1 ⊆ D)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ D) :
    ∃ (f : E × ℝ → M) (U : Set (E × ℝ)) (V : Set E),
      IsOpen U ∧ IsOpen V ∧ (chartAt E (γ 1)) (γ 1) ∈ V ∧
      V ⊆ (chartAt E (γ 1)).target ∧ V ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U ∧
      ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U ∧
      (∀ y, f (y, 0) = γ 0) ∧
      (∀ y, f (y, 1) = (chartAt E (γ 1)).symm y) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) 1, f ((chartAt E (γ 1)) (γ 1), r) = γ r := by
  classical
  let e := chartAt E (γ 1)
  let y0 : E := e (γ 1)
  let D0 := D ∩ γ ⁻¹' e.source
  have hD0 : IsOpen D0 := hγ.continuousOn.isOpen_inter_preimage hD e.open_source
  have h1 : (1 : ℝ) ∈ D0 := ⟨hI ⟨zero_le_one, le_rfl⟩, mem_chart_source E (γ 1)⟩
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hD0.mem_nhds h1)
  obtain ⟨a, hla, ha1⟩ := exists_between (max_lt (show (0 : ℝ) < 1 by norm_num) hlu.1)
  have ha0 : 0 < a := (le_max_left 0 l).trans_lt hla
  have hla' : l < a := (le_max_right 0 l).trans_lt hla
  have htail : Set.Icc a 1 ⊆ D0 := by
    intro r hr
    exact hsub ⟨hla'.trans_le hr.1, hr.2.trans_lt hlu.2⟩
  have hdisjoint : Disjoint (Set.Iic a) ({1} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro r hr hr1
    have hr' : r = 1 := Set.mem_singleton_iff.mp hr1
    exact (not_le_of_gt ha1) (hr' ▸ hr)
  obtain ⟨χ, hzero, hone, _⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, ℝ))
      isClosed_Iic isClosed_singleton hdisjoint (n := ⊤)
  have hχzero (r : ℝ) (hr : r ≤ a) : χ r = 0 := by
    have h : ∀ᶠ t in 𝓝 r, χ t = 0 :=
      (nhds_le_nhdsSet (show r ∈ Set.Iic a from hr)) hzero
    exact h.self_of_nhds
  have hχone : χ (1 : ℝ) = 1 := by
    have h : ∀ᶠ t in 𝓝 (1 : ℝ), χ t = 1 :=
      (nhds_le_nhdsSet (show (1 : ℝ) ∈ ({1} : Set ℝ) from Set.mem_singleton 1)) hone
    exact h.self_of_nhds
  let k : E × ℝ → E := fun z ↦ e (γ z.2) + χ z.2 • (z.1 - y0)
  let f : E × ℝ → M := fun z ↦ if a < z.2 then e.symm (k z) else γ z.2
  let W0 : Set (E × ℝ) := Prod.snd ⁻¹' D0
  let W : Set (E × ℝ) := W0 ∩ k ⁻¹' e.target
  let L : Set (E × ℝ) := Set.univ ×ˢ (D ∩ Set.Iio a)
  let U := L ∪ W
  have hW0 : IsOpen W0 := hD0.preimage continuous_snd
  have hbase : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ (fun z ↦ γ z.2) W0 :=
    hγ.comp contDiff_snd.contMDiff.contMDiffOn (fun z hz ↦ hz.1)
  have hcoord : ContDiffOn ℝ ∞ (fun z : E × ℝ ↦ e (γ z.2)) W0 :=
    (contMDiffOn_chart.comp hbase (fun z hz ↦ hz.2)).contDiffOn
  have hχ : ContDiff ℝ ∞ (fun z : E × ℝ ↦ χ z.2) :=
    χ.contMDiff.contDiff.comp contDiff_snd
  have hk : ContDiffOn ℝ ∞ k W0 :=
    hcoord.add (hχ.smul (contDiff_fst.sub contDiff_const)).contDiffOn
  have hW : IsOpen W := hk.continuousOn.isOpen_inter_preimage hW0 e.open_target
  have hL : IsOpen L := isOpen_univ.prod (hD.inter isOpen_Iio)
  have hfL : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f L := by
    apply (hγ.comp contDiff_snd.contMDiff.contMDiffOn (fun z hz ↦ hz.2.1)).congr
    intro z hz
    have hzlt : z.2 < a := hz.2.2
    simp only [f, if_neg (not_lt.mpr hzlt.le), Function.comp_apply]
  have hfW : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f W := by
    have hcomp := (contMDiffOn_chart_symm (I := 𝓡 n) (x := γ 1)).comp
      (hk.mono Set.inter_subset_left).contMDiffOn (fun z hz ↦ hz.2)
    apply hcomp.congr
    intro z hz
    change f z = e.symm (k z)
    by_cases hr : a < z.2
    · simp only [f, if_pos hr]
    · simp only [f, if_neg hr, k, hχzero z.2 (le_of_not_gt hr), zero_smul, add_zero]
      exact (e.left_inv hz.1.2).symm
  have hU : IsOpen U := hL.union hW
  have hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U :=
    hfL.union_of_isOpen hfW hL hW
  have hsegment : ∀ r ∈ Set.Icc (0 : ℝ) 1, (y0, r) ∈ U := by
    intro r hr
    by_cases hra : r < a
    · exact Or.inl ⟨Set.mem_univ _, hI hr, hra⟩
    · apply Or.inr
      have hr0 := htail ⟨le_of_not_gt hra, hr.2⟩
      refine ⟨hr0, ?_⟩
      change k (y0, r) ∈ e.target
      simpa only [k, sub_self, smul_zero, add_zero] using e.map_source hr0.2
  have hnear : ∀ᶠ y : E in 𝓝 y0, ∀ r ∈ Set.Icc (0 : ℝ) 1, (y, r) ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    exact hU.mem_nhds (hsegment r hr)
  obtain ⟨V0, hVsub, hVopen, hyV⟩ := mem_nhds_iff.mp hnear
  let V := V0 ∩ e.target
  have hyTarget : y0 ∈ e.target := e.map_source (mem_chart_source E (γ 1))
  refine ⟨f, U, V, hU, hVopen.inter e.open_target, ⟨hyV, hyTarget⟩,
    Set.inter_subset_right, ?_, hf, ?_, ?_, ?_⟩
  · intro z hz
    exact hVsub hz.1.1 z.2 hz.2
  · intro y
    simp only [f, if_neg (not_lt.mpr ha0.le)]
  · intro y
    change f (y, 1) = e.symm y
    simp only [f, if_pos ha1, k, hχone, one_smul, y0, add_sub_cancel]
  · intro r hr
    change f (y0, r) = γ r
    by_cases hra : a < r
    · simp only [f, if_pos hra, k, sub_self, smul_zero, add_zero]
      exact e.left_inv (htail ⟨hra.le, hr.2⟩).2
    · simp only [f, if_neg hra]

end PoincareConjecture.Proofs.M09
