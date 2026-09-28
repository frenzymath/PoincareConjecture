import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Flags.FiniteFlagCoordinates








set_option autoImplicit false

open scoped BigOperators
open Set

noncomputable section

universe u v

namespace Poincare.Topology

def finiteCoordinateSupport {V : Type u} [Fintype V] (z : V → Real) : Finset V :=
  Finset.univ.filter (fun v => z v ≠ 0)

theorem mem_finiteCoordinateSupport {V : Type u} [Fintype V]
    (z : V → Real) (v : V) : v ∈ finiteCoordinateSupport z ↔ z v ≠ 0 := by
  simp [finiteCoordinateSupport]

def affineCoordinateSection {V : Type u} [Fintype V]
    {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V) : Set (V → Real) :=
  {z | z ∈ stdSimplex Real V ∧ finiteCoordinateSupport z ⊆ s ∧ A z = 0}

abbrev AffineSectionFace {V : Type u} [Fintype V]
    {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V) :=
  {t : Finset V // ∃ z ∈ affineCoordinateSection A s, finiteCoordinateSupport z = t}

def affineSectionCenter {V : Type u} [Fintype V]
    {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V) (t : AffineSectionFace A s) : V → Real :=
  t.property.choose

theorem affineSectionCenter_spec {V : Type u} [Fintype V]
    {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V) (t : AffineSectionFace A s) :
    affineSectionCenter A s t ∈ affineCoordinateSection A s ∧
      finiteCoordinateSupport (affineSectionCenter A s t) = t.val :=
  t.property.choose_spec

theorem finiteCoordinateSupport_nonempty {V : Type u} [Fintype V]
    (z : V → Real) (hz : z ∈ stdSimplex Real V) :
    (finiteCoordinateSupport z).Nonempty := by
  by_contra hne
  have hzero : ∀ v, z v = 0 := by
    intro v
    by_contra hv
    exact hne ⟨v, (mem_finiteCoordinateSupport z v).mpr hv⟩
  have hsum := hz.2
  simp only [hzero, Finset.sum_const_zero] at hsum
  exact zero_ne_one hsum

theorem exists_affine_section_face_residual
    {V : Type u} [Fintype V]
    {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V)
    (z c : V → Real) (hz : z ∈ affineCoordinateSection A s)
    (hc : c ∈ affineCoordinateSection A s)
    (hsupport : finiteCoordinateSupport z = finiteCoordinateSupport c)
    (hne : z ≠ c) :
    ∃ (a : Real) (y : V → Real), 0 ≤ a ∧ a < 1 ∧
      y ∈ affineCoordinateSection A s ∧
      finiteCoordinateSupport y ⊂ finiteCoordinateSupport z ∧
      z = a • c + (1 - a) • y := by
  classical
  let t := finiteCoordinateSupport z
  have ht : t.Nonempty := finiteCoordinateSupport_nonempty z hz.1
  have hcp (v : V) (hv : v ∈ t) : 0 < c v := by
    have hcv : c v ≠ 0 := (mem_finiteCoordinateSupport c v).mp (hsupport ▸ hv)
    exact lt_of_le_of_ne (hc.1.1 v) (Ne.symm hcv)
  obtain ⟨v0, hv0, hmin⟩ := t.exists_min_image (fun v => z v / c v) ht
  let a := z v0 / c v0
  have ha : 0 ≤ a := div_nonneg (hz.1.1 v0) (hc.1.1 v0)
  have hle (v : V) : a * c v ≤ z v := by
    by_cases hv : v ∈ t
    · exact (le_div_iff₀ (hcp v hv)).mp (hmin v hv)
    · have hzv : z v = 0 := not_ne_iff.mp ((mem_finiteCoordinateSupport z v).not.mp hv)
      have hcv : c v = 0 := by
        apply not_ne_iff.mp
        intro h
        apply hv
        change v ∈ finiteCoordinateSupport z
        rw [hsupport]
        exact (mem_finiteCoordinateSupport c v).mpr h
      simp [hzv, hcv]
  have ha1 : a ≤ 1 := by
    have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hle v)
    simpa only [← Finset.mul_sum, hc.1.2, hz.1.2, mul_one] using hsum
  have halt : a < 1 := by
    refine lt_of_le_of_ne ha1 ?_
    intro heq
    apply hne
    have hpoint := (Finset.sum_eq_sum_iff_of_le
      (fun v (_ : v ∈ (Finset.univ : Finset V)) => hle v)).mp (by
        simp only [← Finset.mul_sum, hc.1.2, hz.1.2, mul_one, heq])
    funext v
    simpa only [heq, one_mul] using (hpoint v (Finset.mem_univ v)).symm
  have hb : 0 < 1 - a := sub_pos.mpr halt
  let y : V → Real := (1 - a)⁻¹ • (z - a • c)
  have hy_apply (v : V) : y v = (z v - a * c v) / (1 - a) := by
    simp only [y, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hynonneg (v : V) : 0 ≤ y v := by
    rw [hy_apply]
    exact div_nonneg (sub_nonneg.mpr (hle v)) hb.le
  have hysum : ∑ v, y v = 1 := by
    simp only [hy_apply, div_eq_mul_inv, ← Finset.sum_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum,
      hz.1.2, hc.1.2, mul_one]
    exact mul_inv_cancel₀ hb.ne'
  have hyplane : A y = 0 := by
    have hy : y = (1 - a)⁻¹ • (z - c) +ᵥ c := by
      funext v
      change (1 - a)⁻¹ * (z v - a * c v) = (1 - a)⁻¹ * (z v - c v) + c v
      field_simp
      ring
    have hlinear : A.linear (z - c) = 0 := by
      simpa only [vsub_eq_sub, hz.2.2, hc.2.2, sub_self] using A.linearMap_vsub z c
    rw [hy, A.map_vadd, map_smul, hlinear, smul_zero, hc.2.2, zero_vadd]
  have hsub : finiteCoordinateSupport y ⊆ t := by
    intro v hv
    by_contra hvt
    have hzv : z v = 0 := not_ne_iff.mp ((mem_finiteCoordinateSupport z v).not.mp hvt)
    have hcv : c v = 0 := by
      apply not_ne_iff.mp
      intro h
      apply hvt
      change v ∈ finiteCoordinateSupport z
      rw [hsupport]
      exact (mem_finiteCoordinateSupport c v).mpr h
    exact ((mem_finiteCoordinateSupport y v).mp hv) (by simp [hy_apply, hzv, hcv])
  have hyv0 : y v0 = 0 := by
    rw [hy_apply]
    have hprod : a * c v0 = z v0 := by
      exact div_mul_cancel₀ _ (hcp v0 hv0).ne'
    rw [hprod, sub_self, zero_div]
  have hstrict : finiteCoordinateSupport y ⊂ t := by
    refine lt_of_le_of_ne hsub ?_
    intro heq
    exact ((mem_finiteCoordinateSupport y v0).mp (heq ▸ hv0)) hyv0
  refine ⟨a, y, ha, halt, ⟨⟨hynonneg, hysum⟩, hsub.trans hz.2.1, hyplane⟩,
    hstrict, ?_⟩
  funext v
  change z v = a * c v + (1 - a) * y v
  rw [hy_apply, mul_div_cancel₀ _ hb.ne']
  ring

theorem exists_affine_section_flag
    {V : Type u} [Fintype V]
    {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V)
    (z : V → Real) (hz : z ∈ affineCoordinateSection A s) :
    ∃ t : Finset (AffineSectionFace A s), t.Nonempty ∧
      (∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) ∧
      (∀ i ∈ t, i.val ⊆ finiteCoordinateSupport z) ∧
      z ∈ convexHull Real (affineSectionCenter A s '' (t : Set (AffineSectionFace A s))) := by
  classical
  have H : ∀ q : Finset V, ∀ z : V → Real,
      z ∈ affineCoordinateSection A s → finiteCoordinateSupport z = q →
      ∃ t : Finset (AffineSectionFace A s), t.Nonempty ∧
        (∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) ∧
        (∀ i ∈ t, i.val ⊆ finiteCoordinateSupport z) ∧
        z ∈ convexHull Real
          (affineSectionCenter A s '' (t : Set (AffineSectionFace A s))) := by
    apply Finset.strongInduction
    intro q ih z hz hq
    let i : AffineSectionFace A s := ⟨q, z, hz, hq⟩
    have hcenter := affineSectionCenter_spec A s i
    by_cases hzi : z = affineSectionCenter A s i
    · refine ⟨{i}, Finset.singleton_nonempty i, ?_, ?_, ?_⟩
      · intro j hj k hk
        obtain rfl := Finset.mem_singleton.mp hj
        obtain rfl := Finset.mem_singleton.mp hk
        exact Or.inl le_rfl
      · intro j hj
        obtain rfl := Finset.mem_singleton.mp hj
        change q ⊆ finiteCoordinateSupport z
        exact hq.symm.subset
      · rw [hzi]
        exact subset_convexHull Real _ (Set.mem_image_of_mem _ (Finset.mem_singleton_self i))
    · obtain ⟨a, y, ha, ha1, hy, hsub, hdecomp⟩ :=
        exists_affine_section_face_residual A s z (affineSectionCenter A s i)
          hz hcenter.1 (hq.trans hcenter.2.symm) hzi
      have hyq : finiteCoordinateSupport y ⊂ q := by simpa only [hq] using hsub
      obtain ⟨t, ht, hchain, hsmall, hyhull⟩ :=
        ih (finiteCoordinateSupport y) hyq y hy rfl
      refine ⟨insert i t, Finset.insert_nonempty i t, ?_, ?_, ?_⟩
      · intro j hj k hk
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rcases Finset.mem_insert.mp hk with rfl | hk
          · exact Or.inl le_rfl
          · exact Or.inr (show k.val ⊆ q from (hsmall k hk).trans hyq.subset)
        · rcases Finset.mem_insert.mp hk with rfl | hk
          · exact Or.inl (show j.val ⊆ q from (hsmall j hj).trans hyq.subset)
          · exact hchain j hj k hk
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · change q ⊆ finiteCoordinateSupport z
          exact hq.symm.subset
        · exact (hsmall j hj).trans hsub.subset
      · have hc_mem : affineSectionCenter A s i ∈ convexHull Real
            (affineSectionCenter A s '' (↑(insert i t) : Set (AffineSectionFace A s))) :=
          subset_convexHull Real _ (Set.mem_image_of_mem _ (Finset.mem_insert_self i t))
        have hy_mem : y ∈ convexHull Real
            (affineSectionCenter A s '' (↑(insert i t) : Set (AffineSectionFace A s))) := by
          apply convexHull_mono _ hyhull
          exact Set.image_mono (by
            intro j hj
            exact Finset.mem_insert_of_mem hj)
        rw [hdecomp]
        exact (convex_convexHull Real _) hc_mem hy_mem ha (sub_nonneg.mpr ha1.le) (by ring)
  exact H (finiteCoordinateSupport z) z hz rfl

theorem convex_affineCoordinateSection
    {V : Type u} [Fintype V]
    {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V) :
    Convex Real (affineCoordinateSection A s) := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_stdSimplex Real V) hx.1 hy.1 ha hb hab, ?_, ?_⟩
  · intro v hv
    by_contra hvs
    have hxv : x v = 0 := by
      apply not_ne_iff.mp
      intro hvx
      exact hvs (hx.2.1 ((mem_finiteCoordinateSupport x v).mpr hvx))
    have hyv : y v = 0 := by
      apply not_ne_iff.mp
      intro hvy
      exact hvs (hy.2.1 ((mem_finiteCoordinateSupport y v).mpr hvy))
    exact ((mem_finiteCoordinateSupport (a • x + b • y) v).mp hv) (by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hxv, hyv, mul_zero, add_zero])
  · have hfiber : Convex Real {z : V → Real | A z = 0} :=
      (convex_singleton (0 : F)).affine_preimage A
    exact hfiber hx.2.2 hy.2.2 ha hb hab

open scoped Classical in
theorem affineSectionFlagMap_range
    {V : Type u} [Fintype V]
    {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V) :
    Set.range (finiteOrderComplexMap (AffineSectionFace A s) (affineSectionCenter A s)) =
      affineCoordinateSection A s := by
  classical
  let I := AffineSectionFace A s
  let c := affineSectionCenter A s
  apply Set.Subset.antisymm
  · rintro z ⟨w, rfl⟩
    have hw := (finiteOrderComplex_space I w.val).mp w.property
    exact (convex_affineCoordinateSection A s).sum_mem
      (fun i _ => hw.1 i) hw.2.1 (fun i _ => (affineSectionCenter_spec A s i).1)
  · intro z hz
    obtain ⟨t, ht, hchain, _, hzhull⟩ := exists_affine_section_flag A s z hz
    let L : (I → Real) →ₗ[Real] (V → Real) := Fintype.linearCombination Real c
    let basisPoint : I → I → Real := fun i => Pi.single i 1
    have himage : L '' convexHull Real (basisPoint '' (t : Set I)) =
        convexHull Real (c '' (t : Set I)) := by
      rw [L.image_convexHull, Set.image_image]
      congr 1
      have heval : (fun i => L (basisPoint i)) = c := by
        funext i
        simp only [L, basisPoint, Fintype.linearCombination_apply_single, one_smul]
      exact congrArg (fun f : I → V → Real => f '' (t : Set I)) heval
    have hzimage : z ∈ L '' convexHull Real (basisPoint '' (t : Set I)) := by
      rw [himage]
      exact hzhull
    obtain ⟨w, hw, hwz⟩ := hzimage
    have hface : t.image basisPoint ∈ (finiteOrderComplex I).faces := by
      apply (finiteOrderComplex_faces I _).mpr
      refine ⟨t, ht, hchain, ?_⟩
      apply Finset.image_congr
      intro i hi
      funext j
      simp only [basisPoint, Pi.single_apply]
      split_ifs <;> rfl
    have hwspace : w ∈ (finiteOrderComplex I).space := by
      apply Geometry.SimplicialComplex.convexHull_subset_space hface
      simpa only [Finset.coe_image] using hw
    refine ⟨⟨w, hwspace⟩, ?_⟩
    exact hwz

open scoped Classical in
def affineSectionFlagHomeomorph
    {V : Type u} [Fintype V]
    {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V) :
    (finiteOrderComplex (AffineSectionFace A s)).space ≃ₜ affineCoordinateSection A s := by
  let I := AffineSectionFace A s
  let c := affineSectionCenter A s
  have hsupport : ∀ i : I, (i.val).Nonempty := by
    intro i
    have hs := affineSectionCenter_spec A s i
    rw [← hs.2]
    exact finiteCoordinateSupport_nonempty (c i) hs.1.1
  have hc_nonneg : ∀ (i : I) v, 0 ≤ c i v :=
    fun i v => (affineSectionCenter_spec A s i).1.1.1 v
  have hc_pos : ∀ (i : I) v, 0 < c i v ↔ v ∈ i.val := by
    intro i v
    rw [← (affineSectionCenter_spec A s i).2, mem_finiteCoordinateSupport]
    exact ⟨ne_of_gt, fun h => lt_of_le_of_ne (hc_nonneg i v) (Ne.symm h)⟩
  let h := finiteOrderComplexMap_homeomorph_range_of_supports c Subtype.val
    hsupport (fun i j => Iff.rfl) hc_nonneg hc_pos
  exact h.trans (Homeomorph.setCongr (affineSectionFlagMap_range A s))

end Poincare.Topology
