import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcParameter
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcPush
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcRegionCrossing
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Group.Nat.Even

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

def polygonArcContactGap {n m : ℕ} (c : Fin m ↪ Fin (n + 2))
    (σ : Fin m ≃ Fin m) (j : Fin (m + 1)) : Set ℝ :=
  (if hj : 0 < j.val then Ioi ((c (σ ⟨j.val - 1, by omega⟩)).val : ℝ) else Ici 0) ∩
  (if hj : j.val < m then Iio ((c (σ ⟨j.val, hj⟩)).val : ℝ) else Iic (n + 1 : ℕ))

private theorem exists_sorted_contact_permutation {n m : ℕ}
    (c : Fin m ↪ Fin (n + 2)) :
    ∃ σ : Fin m ≃ Fin m, StrictMono (fun j => (c (σ j)).val) := by
  classical
  let U : Finset (Fin (n + 2)) := Finset.univ.image c
  have hcard : U.card = m := by
    simp only [U, Finset.card_image_of_injective _ c.injective,
      Finset.card_univ, Fintype.card_fin]
  let f : Fin m → U := fun i => ⟨c i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact c.injective (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
      exact ⟨i, Subtype.ext hi⟩
  let e : Fin m ≃ U := Equiv.ofBijective f hf
  let σ := (U.orderIsoOfFin hcard).toEquiv.trans e.symm
  have heq (j : Fin m) : c (σ j) = U.orderEmbOfFin hcard j := by
    change (e (e.symm (U.orderIsoOfFin hcard j))).val = _
    rw [e.apply_symm_apply]
    rfl
  refine ⟨σ, ?_⟩
  intro i j hij
  change (c (σ i)).val < (c (σ j)).val
  rw [heq, heq]
  exact (U.orderEmbOfFin hcard).strictMono hij

private theorem contact_gap_properties {n m : ℕ} (hm : 0 < m)
    (c : Fin m ↪ Fin (n + 2)) (σ : Fin m ≃ Fin m)
    (hσ : StrictMono (fun j => (c (σ j)).val))
    (hint : ∀ i, 0 < (c i).val ∧ (c i).val < n + 1) :
    (∀ j : Fin (m + 1), (polygonArcContactGap c σ j).Nonempty ∧
      IsPreconnected (polygonArcContactGap c σ j) ∧
      polygonArcContactGap c σ j ⊆ Icc (0 : ℝ) (n + 1 : ℕ) ∧
      ∀ t ∈ polygonArcContactGap c σ j, ∀ i : Fin m, t ≠ ((c i).val : ℝ)) ∧
    (0 : ℝ) ∈ polygonArcContactGap c σ 0 ∧
    ((n + 1 : ℕ) : ℝ) ∈ polygonArcContactGap c σ (Fin.last m) ∧
    (∀ j : Fin m, ∀ u ∈ Ioo (0 : ℝ) 1,
      (c (σ j)).val - u ∈ polygonArcContactGap c σ j.castSucc ∧
      (c (σ j)).val + u ∈ polygonArcContactGap c σ j.succ) := by
  let T : Fin m → ℝ := fun j => (c (σ j)).val
  have hT (j : Fin m) : 0 < T j ∧ T j < (n + 1 : ℕ) := by
    dsimp only [T]
    exact_mod_cast hint (σ j)
  have hTmono : StrictMono T := by
    intro i j hij
    dsimp only [T]
    exact_mod_cast hσ hij
  have hstep {i j : Fin m} (hij : i < j) : T i + 1 ≤ T j := by
    dsimp only [T]
    exact_mod_cast (show (c (σ i)).val + 1 ≤ (c (σ j)).val from hσ hij)
  have hfirst : (0 : ℝ) ∈ polygonArcContactGap c σ 0 := by
    simpa [polygonArcContactGap, hm, T] using (hT ⟨0, hm⟩).1
  have hlast : ((n + 1 : ℕ) : ℝ) ∈ polygonArcContactGap c σ (Fin.last m) := by
    simpa only [polygonArcContactGap, Fin.val_last, dif_pos hm, lt_self_iff_false,
      dite_false, mem_inter_iff, mem_Ioi, mem_Iic, le_refl, and_true] using
      (hT ⟨m - 1, by omega⟩).2
  have hsample (j : Fin m) (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      T j - u ∈ polygonArcContactGap c σ j.castSucc ∧
      T j + u ∈ polygonArcContactGap c σ j.succ := by
    constructor
    · simp only [polygonArcContactGap, Fin.val_castSucc, dif_pos j.isLt]
      change T j - u ∈ (if hj : 0 < j.val then
        Ioi (T ⟨j.val - 1, by omega⟩) else Ici 0) ∩ Iio (T j)
      refine ⟨?_, by change T j - u < T j; linarith [hu.1]⟩
      by_cases hj : 0 < j.val
      · rw [dif_pos hj]
        have := hstep (i := ⟨j.val - 1, by omega⟩) (j := j)
          (by change j.val - 1 < j.val; omega)
        change T ⟨j.val - 1, by omega⟩ < T j - u
        linarith [hu.2]
      · rw [dif_neg hj]
        have hjT : (1 : ℝ) ≤ T j := by
          dsimp only [T]
          exact_mod_cast (hint (σ j)).1
        change 0 ≤ T j - u
        linarith [hu.2]
    · change T j + u ∈ Ioi (T j) ∩ (if hj : j.val + 1 < m then
        Iio (T ⟨j.val + 1, hj⟩) else Iic (n + 1 : ℕ))
      refine ⟨by change T j < T j + u; linarith [hu.1], ?_⟩
      by_cases hj : j.val + 1 < m
      · rw [dif_pos hj]
        have := hstep (i := j) (j := ⟨j.val + 1, hj⟩)
          (by change j.val < j.val + 1; omega)
        change T j + u < T ⟨j.val + 1, hj⟩
        linarith [hu.2]
      · rw [dif_neg hj]
        have hjT : T j + 1 ≤ (n + 1 : ℕ) := by
          dsimp only [T]
          exact_mod_cast (show (c (σ j)).val + 1 ≤ n + 1 from (hint (σ j)).2)
        change T j + u ≤ (n + 1 : ℕ)
        linarith [hu.2]
  refine ⟨?_, hfirst, hlast, hsample⟩
  intro j
  have hne : (polygonArcContactGap c σ j).Nonempty := by
    by_cases hj0 : j.val = 0
    · have heq : j = 0 := Fin.ext hj0
      exact ⟨0, heq.symm ▸ hfirst⟩
    · by_cases hjm : j.val = m
      · have heq : j = Fin.last m := Fin.ext hjm
        exact ⟨(n + 1 : ℕ), heq.symm ▸ hlast⟩
      · have hj : j.val < m := by omega
        have hjpos : 0 < j.val := by omega
        let a : Fin m := ⟨j.val - 1, by omega⟩
        let b : Fin m := ⟨j.val, hj⟩
        have hab : T a < T b := hTmono (by change j.val - 1 < j.val; omega)
        refine ⟨(T a + T b) / 2, ?_⟩
        simp only [polygonArcContactGap, dif_pos hjpos, dif_pos hj, mem_inter_iff,
          mem_Ioi, mem_Iio]
        change T a < (T a + T b) / 2 ∧ (T a + T b) / 2 < T b
        constructor <;> linarith
  have hpre : IsPreconnected (polygonArcContactGap c σ j) := by
    unfold polygonArcContactGap
    split_ifs
    · exact isPreconnected_Ioo
    · exact isPreconnected_Ioc
    · exact isPreconnected_Ico
    · exact isPreconnected_Icc
  have hbound : polygonArcContactGap c σ j ⊆ Icc (0 : ℝ) (n + 1 : ℕ) := by
    intro x hx
    unfold polygonArcContactGap at hx
    constructor
    · by_cases hj : 0 < j.val
      · rw [dif_pos hj] at hx
        exact (hT _).1.le.trans hx.1.le
      · rw [dif_neg hj] at hx
        exact hx.1
    · by_cases hj : j.val < m
      · rw [dif_pos hj] at hx
        exact hx.2.le.trans (hT _).2.le
      · rw [dif_neg hj] at hx
        exact hx.2
  refine ⟨hne, hpre, hbound, ?_⟩
  intro x hx i hxi
  have hxi' : x = T (σ.symm i) := by simpa only [T, Equiv.apply_symm_apply] using hxi
  unfold polygonArcContactGap at hx
  by_cases hi : (σ.symm i).val < j.val
  · have hj : 0 < j.val := by omega
    rw [dif_pos hj] at hx
    have hle : T (σ.symm i) ≤ T ⟨j.val - 1, by omega⟩ :=
      hTmono.monotone (by change (σ.symm i).val ≤ j.val - 1; omega)
    exact (not_lt_of_ge hle) (hxi' ▸ hx.1)
  · have hj : j.val < m := by have := (σ.symm i).isLt; omega
    rw [dif_pos hj] at hx
    have hle : T ⟨j.val, hj⟩ ≤ T (σ.symm i) :=
      hTmono.monotone (by change j.val ≤ (σ.symm i).val; omega)
    exact (not_lt_of_ge hle) (hxi' ▸ hx.2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contact_parameter_neighbors {n : ℕ} (p : Polygon E (n + 2))
    (k : Fin (n + 2)) (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    polygonLinearParameter p ((k.val : ℝ) - u) =
        AffineMap.lineMap (p k) (p ((finRotate (n + 2)).symm k)) u ∧
    polygonLinearParameter p ((k.val : ℝ) + u) =
        AffineMap.lineMap (p k) (p (finRotate (n + 2) k)) u := by
  obtain ⟨i, j, hik, hjk, hip, hjs, _⟩ := exists_arc_incident_edge_indices k hk0 hkl
  have hedge (a : Fin (n + 1)) {t : ℝ}
      (ht : t ∈ Icc (a.val : ℝ) ((a.val : ℝ) + 1)) :
      polygonLinearParameter p t = AffineMap.lineMap (p a.castSucc) (p a.succ)
        (t - a.val) := by
    have ha : polygonIntegerIndex (n + 2) (a.val : ℤ) = a.castSucc :=
      polygonIntegerIndex_nat a.castSucc
    have hnext : finRotate (n + 2) a.castSucc = a.succ := finRotate_of_lt a.isLt
    simpa only [ha, Int.cast_natCast, Polygon.edgePath, hnext] using
      polygonLinearParameter_eq_edge p (a.val : ℤ) (by simpa only [Int.cast_natCast] using ht)
  have hi : (k.val : ℝ) = (i.val : ℝ) + 1 := by
    have hv := congrArg Fin.val hik
    simp only [Fin.val_succ] at hv
    exact_mod_cast hv.symm
  have hj : (k.val : ℝ) = (j.val : ℝ) := by
    exact_mod_cast (congrArg Fin.val hjk).symm
  constructor
  · rw [hedge i (by rw [hi]; constructor <;> linarith [hu.1, hu.2]), hik, hip]
    rw [show (k.val : ℝ) - u - i.val = 1 - u by rw [hi]; ring,
      AffineMap.lineMap_apply_one_sub]
  · rw [hedge j (by rw [hj]; constructor <;> linarith [hu.1, hu.2]), hjk, hjs]
    congr 1
    rw [hj]
    ring

variable [FiniteDimensional ℝ E]

theorem IsSimplePolygonalArc.exists_alternating_contact_gaps {n m : ℕ}
    {p : Polygon E (n + 2)} {r : Polygon E m}
    (hp : IsSimplePolygonalArc p) (hr : IsSimplePolygon r)
    (hdim : Module.finrank ℝ E = 2) (c : Fin m ↪ Fin (n + 2))
    (hc : ∀ i, r i = p (c i))
    (hint : ∀ i, c i ≠ 0 ∧ c i ≠ Fin.last (n + 1))
    (hcontact : r.boundary ℝ ∩ polygonArcBoundary p = range r)
    (hfirst : p 0 ∈ polygonExterior r)
    (hlast : p (Fin.last (n + 1)) ∈ polygonExterior r)
    (hcross : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∃ W A B : Set E,
      IsOpen W ∧ r i ∈ W ∧ IsPreconnected A ∧ IsPreconnected B ∧
      A ∪ B = W \ r.boundary ℝ ∧
      (∀ u ∈ Ioo 0 ε, AffineMap.lineMap (r i)
        (p ((finRotate (n + 2)).symm (c i))) u ∈ A) ∧
      (∀ u ∈ Ioo 0 ε, AffineMap.lineMap (r i)
        (p (finRotate (n + 2) (c i))) u ∈ B)) :
    ∃ σ : Fin m ≃ Fin m,
      StrictMono (fun j => (c (σ j)).val) ∧ Even m ∧ 4 ≤ m ∧
      (∀ t ∈ Icc (0 : ℝ) (n + 1 : ℕ), polygonLinearParameter p t ∈ r.boundary ℝ ↔
        ∃ i : Fin m, t = ((c i).val : ℝ)) ∧
      (∀ i, 0 < (c i).val ∧ (c i).val < n + 1) ∧
      (∀ i j : Fin m, i < j → (c (σ i)).val + 1 ≤ (c (σ j)).val) ∧
      (∀ j : Fin (m + 1), (polygonArcContactGap c σ j).Nonempty ∧
        IsPreconnected (polygonArcContactGap c σ j) ∧
        polygonArcContactGap c σ j ⊆ Icc (0 : ℝ) (n + 1 : ℕ) ∧
        (∀ t ∈ polygonArcContactGap c σ j, ∀ i : Fin m, t ≠ ((c i).val : ℝ)) ∧
        (Even j.val → polygonLinearParameter p '' polygonArcContactGap c σ j ⊆
          polygonExterior r) ∧
        (¬ Even j.val → polygonLinearParameter p '' polygonArcContactGap c σ j ⊆
          polygonInterior r)) ∧
      (0 : ℝ) ∈ polygonArcContactGap c σ 0 ∧
      ((n + 1 : ℕ) : ℝ) ∈ polygonArcContactGap c σ (Fin.last m) ∧
      (∀ j : Fin m, ∀ u ∈ Ioo (0 : ℝ) 1,
        (c (σ j)).val - u ∈ polygonArcContactGap c σ j.castSucc ∧
        (c (σ j)).val + u ∈ polygonArcContactGap c σ j.succ) := by
  have hm3 := hr.three_le
  have hm : 0 < m := by omega
  have hindex (i : Fin (n + 2)) : (i.val : ℝ) ∈ Icc (0 : ℝ) (n + 1 : ℕ) :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast (show i.val ≤ n + 1 from by omega)⟩
  have hintN (i : Fin m) : 0 < (c i).val ∧ (c i).val < n + 1 := by
    refine ⟨Nat.pos_of_ne_zero (fun h => (hint i).1 (Fin.ext h)), ?_⟩
    exact Fin.lt_last_iff_ne_last.mpr (hint i).2
  have htimes (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (n + 1 : ℕ)) :
      polygonLinearParameter p t ∈ r.boundary ℝ ↔
        ∃ i : Fin m, t = ((c i).val : ℝ) := by
    constructor
    · intro htr
      have htp : polygonLinearParameter p t ∈ polygonArcBoundary p :=
        image_polygonLinearParameter_arc p ▸ ⟨t, ht, rfl⟩
      obtain ⟨i, hi⟩ := (show polygonLinearParameter p t ∈ range r from
        hcontact ▸ ⟨htr, htp⟩)
      exact ⟨i, hp.injOn_polygonLinearParameter ht (hindex (c i))
        (hi.symm.trans ((hc i).trans (polygonLinearParameter_natVertex p (c i)).symm))⟩
    · rintro ⟨i, rfl⟩
      rw [polygonLinearParameter_natVertex, ← hc i]
      exact polygon_vertex_mem_boundary r i
  obtain ⟨σ, hσ⟩ := exists_sorted_contact_permutation c
  obtain ⟨hg, hg0, hgm, hsample⟩ := contact_gap_properties hm c σ hσ hintN
  have hΓ : Continuous (polygonLinearParameter p) := by
    exact (continuous_polygonLinearParameter (p := fun _ : Unit => p)
      (fun _ => continuous_const)).comp
      ((continuous_const : Continuous (fun _ : ℝ => ())).prodMk continuous_id)
  obtain ⟨hI, hO, _, _, hdis, hcover, _⟩ := hr.polygonRegions_spec hdim
  have hgapcover (j : Fin (m + 1)) :
      polygonLinearParameter p '' polygonArcContactGap c σ j ⊆
        polygonInterior r ∪ polygonExterior r := by
    rw [hcover]
    rintro _ ⟨t, ht, rfl⟩ htr
    obtain ⟨i, hi⟩ := (htimes t ((hg j).2.2.1 ht)).mp htr
    exact (hg j).2.2.2 t ht i hi
  have hgapI (j : Fin (m + 1)) {x : E}
      (hx : x ∈ polygonLinearParameter p '' polygonArcContactGap c σ j)
      (hxI : x ∈ polygonInterior r) :
      polygonLinearParameter p '' polygonArcContactGap c σ j ⊆ polygonInterior r :=
    ((hg j).2.1.image _ hΓ.continuousOn).subset_left_of_subset_union
      hI hO hdis (hgapcover j) ⟨x, hx, hxI⟩
  have hgapO (j : Fin (m + 1)) {x : E}
      (hx : x ∈ polygonLinearParameter p '' polygonArcContactGap c σ j)
      (hxO : x ∈ polygonExterior r) :
      polygonLinearParameter p '' polygonArcContactGap c σ j ⊆ polygonExterior r :=
    ((hg j).2.1.image _ hΓ.continuousOn).subset_right_of_subset_union
      hI hO hdis (hgapcover j) ⟨x, hx, hxO⟩
  have hΓ0 : polygonLinearParameter p 0 = p 0 := by
    simpa only [Fin.val_zero, Nat.cast_zero] using polygonLinearParameter_natVertex p 0
  have hΓN : polygonLinearParameter p (n + 1 : ℕ) = p (Fin.last (n + 1)) := by
    simpa only [Fin.val_last] using polygonLinearParameter_natVertex p (Fin.last (n + 1))
  have hstart : polygonLinearParameter p '' polygonArcContactGap c σ 0 ⊆
      polygonExterior r := hgapO 0 ⟨0, hg0, rfl⟩ (hΓ0.symm ▸ hfirst)
  have halternate (j : Fin m) :
      (polygonLinearParameter p '' polygonArcContactGap c σ j.castSucc ⊆ polygonExterior r →
        polygonLinearParameter p '' polygonArcContactGap c σ j.succ ⊆ polygonInterior r) ∧
      (polygonLinearParameter p '' polygonArcContactGap c σ j.castSucc ⊆ polygonInterior r →
        polygonLinearParameter p '' polygonArcContactGap c σ j.succ ⊆ polygonExterior r) := by
    obtain ⟨ε, hε, W, A, B, hW, hqW, hA, hB, hlocal, hleft, hright⟩ := hcross (σ j)
    have hlocalregions := hr.opposite_local_rays_regions hdim (r (σ j))
      (p ((finRotate (n + 2)).symm (c (σ j)))) (p (finRotate (n + 2) (c (σ j))))
      ε W A B (polygon_vertex_mem_boundary r (σ j)) hε hW hqW hA hB hlocal hleft hright
    let u := min ε 1 / 2
    have hu0 : 0 < u := div_pos (lt_min hε zero_lt_one) (by norm_num)
    have huε : u < ε := by
      have := min_le_left ε (1 : ℝ)
      dsimp only [u] at hu0 ⊢
      linarith
    have hu1 : u < 1 := by
      have := min_le_right ε (1 : ℝ)
      dsimp only [u] at hu0 ⊢
      linarith
    have hvalues := contact_parameter_neighbors p (c (σ j)) (hint (σ j)).1
      (hint (σ j)).2 ⟨hu0.le, hu1.le⟩
    rw [← hc (σ j)] at hvalues
    have hL : polygonLinearParameter p ((c (σ j)).val - u) ∈
        polygonLinearParameter p '' polygonArcContactGap c σ j.castSucc :=
      ⟨(c (σ j)).val - u, (hsample j u ⟨hu0, hu1⟩).1, rfl⟩
    have hR : polygonLinearParameter p ((c (σ j)).val + u) ∈
        polygonLinearParameter p '' polygonArcContactGap c σ j.succ :=
      ⟨(c (σ j)).val + u, (hsample j u ⟨hu0, hu1⟩).2, rfl⟩
    have hregions :
        (polygonLinearParameter p ((c (σ j)).val - u) ∈ polygonInterior r ∧
          polygonLinearParameter p ((c (σ j)).val + u) ∈ polygonExterior r) ∨
        (polygonLinearParameter p ((c (σ j)).val - u) ∈ polygonExterior r ∧
          polygonLinearParameter p ((c (σ j)).val + u) ∈ polygonInterior r) := by
      rw [hvalues.1, hvalues.2]
      rcases hlocalregions with hi | ho
      · exact Or.inl ⟨hi.1 u ⟨hu0, huε⟩, hi.2 u ⟨hu0, huε⟩⟩
      · exact Or.inr ⟨ho.1 u ⟨hu0, huε⟩, ho.2 u ⟨hu0, huε⟩⟩
    rcases hregions with hreg | hreg
    · exact ⟨fun hh => (Set.disjoint_left.mp hdis hreg.1 (hh hL)).elim,
        fun _ => hgapO j.succ hR hreg.2⟩
    · exact ⟨fun _ => hgapI j.succ hR hreg.2,
        fun hh => (Set.disjoint_left.mp hdis (hh hL) hreg.1).elim⟩
  have hlabels : ∀ a : ℕ, ∀ ha : a ≤ m,
      (Even a → polygonLinearParameter p '' polygonArcContactGap c σ ⟨a, by omega⟩ ⊆
        polygonExterior r) ∧
      (¬ Even a → polygonLinearParameter p '' polygonArcContactGap c σ ⟨a, by omega⟩ ⊆
        polygonInterior r) := by
    intro a
    induction a with
    | zero =>
        intro ha
        exact ⟨fun _ => hstart, fun hh => (hh ⟨0, rfl⟩).elim⟩
    | succ a ih =>
        intro ha
        have ham : a < m := by omega
        have hprev := ih (by omega)
        have hnext := halternate ⟨a, ham⟩
        constructor
        · intro he
          exact hnext.2 (hprev.2 (Nat.even_add_one.mp he))
        · intro hne
          have he : Even a := by
            by_contra hh
            exact hne (Nat.even_add_one.mpr hh)
          exact hnext.1 (hprev.1 he)
  have heven : Even m := by
    by_contra hodd
    exact Set.disjoint_left.mp hdis
      ((hlabels m le_rfl).2 hodd ⟨(n + 1 : ℕ), hgm, rfl⟩) (hΓN.symm ▸ hlast)
  have hfour : 4 ≤ m := by
    have := Nat.even_iff.mp heven
    omega
  refine ⟨σ, hσ, heven, hfour, htimes, hintN, ?_, ?_, hg0, hgm, hsample⟩
  · intro i j hij
    exact hσ hij
  · intro j
    exact ⟨(hg j).1, (hg j).2.1, (hg j).2.2.1, (hg j).2.2.2,
      (hlabels j.val (by omega)).1, (hlabels j.val (by omega)).2⟩

end PoincareConjecture.M25.Topology3D
