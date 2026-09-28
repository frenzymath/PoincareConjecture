import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarCoreMap
import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarShellMap
import PoincareConjecture.Proofs.M76.Rigidity.OriginalCubeShellGluing

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V3) 1
local notation "Q0" => sphere (0 : V3) (7 / 8)
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (0 : ℝ) (1 / 8)
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7 / 8) 1

theorem ChartwisePLBall.attach_outer_strip
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {D : Set X}
    (hcover_e : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (b : ChartwisePLBall e D (c '' (L.space ×ˢ {eps})))
    (hoverlap : D ∩ c '' (L.space ×ˢ Icc 0 eps) = c '' (L.space ×ˢ {eps})) :
    Nonempty (ChartwisePLBall e (D ∪ c '' (L.space ×ˢ Icc 0 eps))
      (c '' (L.space ×ˢ {0}))) ∧
      D ⊆ interior (D ∪ c '' (L.space ×ˢ Icc 0 eps)) := by
  have hlevel (z : E × ℝ) (hz : z ∈ L.space ×ˢ I)
      (t : ℝ) (ht : t ∈ I) : c z ∈ c '' (L.space ×ˢ {t}) ↔ z.2 = t := by
    constructor
    · rintro ⟨w, hw, hweq⟩
      have hwt : w.2 = t := hw.2
      have hwI : w ∈ L.space ×ˢ I := ⟨hw.1, hwt.symm ▸ ht⟩
      have heq := hi.injective (a₁ := ⟨w, hwI⟩) (a₂ := ⟨z, hz⟩) hweq
      exact (congrArg (fun v : (L.space ×ˢ I : Set (E × ℝ)) => v.1.2) heq).symm.trans hwt
    · intro hzt
      exact ⟨z, ⟨hz.1, hzt⟩, rfl⟩
  have houterSub : c '' (L.space ×ˢ {(0 : ℝ)}) ⊆ c '' (L.space ×ˢ Icc 0 eps) := by
    apply image_mono
    exact prod_mono Subset.rfl (singleton_subset_iff.mpr ⟨le_rfl, heps.le⟩)
  have hDouter : Disjoint D (c '' (L.space ×ˢ {(0 : ℝ)})) := by
    apply disjoint_left.mpr
    rintro x hxD ⟨z, hz, rfl⟩
    have hztime : z.2 = 0 := hz.2
    have hzI : z ∈ L.space ×ˢ I := ⟨hz.1, by rw [hztime]; norm_num⟩
    have hzold := hoverlap.subset ⟨hxD, houterSub ⟨z, hz, rfl⟩⟩
    have hzeps := (hlevel z hzI eps ⟨heps.le, heps1⟩).mp hzold
    exact heps.ne' (hzeps.symm.trans hztime)
  obtain ⟨qH, hqH, hqvalue⟩ := b.exists_finitePL_collar_level_parameter
    hcompat L hL c hc hi ⟨heps.le, heps1⟩
  obtain ⟨h, hh, _, hnorm, _⟩ := exists_unitCube_inward_finitePL_collar
  obtain ⟨beta, A, _, hA, hbeta, hAbeta, hAmem⟩ :=
    exists_finitePL_cube_collar_inner_extension h hh hnorm
  obtain ⟨f0, h0, hi0, him0, _, h0value⟩ := b.exists_inner_cube_map beta A hA hAbeta hAmem
  obtain ⟨f1, h1, hi1, him1, h1value⟩ :=
    exists_original_collar_shell_map L c hc hi qH hqH h hh heps heps1
  have hshell (z : (Q ×ˢ J : Set (V3 × ℝ))) :
      ((qH ⟨z.1.1, z.property.1⟩ : E), 8 * eps * z.1.2) ∈ L.space ×ˢ I := by
    refine ⟨(qH ⟨z.1.1, z.property.1⟩).property, ?_, ?_⟩
    · exact mul_nonneg (mul_nonneg (by norm_num) heps.le) z.property.2.1
    · have hz := z.property.2.2
      nlinarith
  have h1ends (x : V3) (hx : x ∈ T) :
      (f1 x ∈ c '' (L.space ×ˢ {eps}) ↔ x ∈ Q0) ∧
      (f1 x ∈ c '' (L.space ×ˢ {(0 : ℝ)}) ↔ x ∈ Q) := by
    let z := h.symm ⟨x, hx⟩
    have hzx : (h z : V3) = x := congrArg Subtype.val (h.apply_symm_apply ⟨x, hx⟩)
    rw [← hzx, h1value]
    rw [hlevel _ (hshell z) eps ⟨heps.le, heps1⟩,
      hlevel _ (hshell z) 0 (by norm_num)]
    change (8 * eps * z.1.2 = eps ↔ (h z : V3) ∈ Q0) ∧
      (8 * eps * z.1.2 = 0 ↔ (h z : V3) ∈ Q)
    simp only [mem_sphere_zero_iff_norm, hnorm]
    constructor <;> constructor <;> intro ht <;> nlinarith [z.property.2.1, z.property.2.2]
  have hagree : EqOn f0 f1 Q0 := by
    intro x hx
    let z : Q := beta.symm ⟨x, hx⟩
    have hbetax : (beta z : V3) = x := congrArg Subtype.val (beta.apply_symm_apply ⟨x, hx⟩)
    calc
      f0 x = f0 (beta z) := congrArg f0 hbetax.symm
      _ = b.map z := h0value z
      _ = c ((qH z : E), eps) := (hqvalue z).symm
      _ = f1 (beta z) := by
        rw [hbeta z, h1value]
        change c ((qH z : E), eps) = c ((qH z : E), 8 * eps * (1 / 8))
        rw [show 8 * eps * (1 / 8 : ℝ) = eps by ring]
      _ = f1 x := congrArg f1 hbetax
  obtain ⟨_, ⟨K, hK, hKT, _⟩, _⟩ := hh.symm
  obtain ⟨bnew⟩ := exists_chartwisePLBall_of_marked_cube_shell hcover_e hcompat K hK hKT
    rfl hoverlap (houterSub.trans subset_union_right) hDouter
    f0 f1 h0 h1 hi0 hi1 him0 him1
    (fun x hx => (h1ends x hx).1) (fun x hx => (h1ends x hx).2) hagree
  refine ⟨⟨bnew⟩, ?_⟩
  rw [bnew.interior_eq_sdiff]
  exact fun x hx => ⟨Or.inl hx, fun hout => disjoint_left.mp hDouter hx hout⟩

end PoincareConjecture.M76
