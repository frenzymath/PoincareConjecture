import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcInsideGaps
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcSubarc
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcTerminalClosure

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

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

private theorem sorted_adjacent_contact_ranks {n m : ℕ}
    (c : Fin m ↪ Fin (n + 2)) (τ : Fin m ≃ Fin m)
    (hτ : StrictMono (fun j => (c (τ j)).val))
    (a b : Fin m) (hab : (c a).val + 1 = (c b).val) :
    (τ.symm a).val + 1 = (τ.symm b).val := by
  have hlt : τ.symm a < τ.symm b := by
    by_contra hn
    have hh := hτ.monotone (le_of_not_gt hn)
    simp only [τ.apply_symm_apply] at hh
    omega
  by_contra hn
  let j : Fin m := ⟨(τ.symm a).val + 1, by have := (τ.symm b).isLt; omega⟩
  have hleft := hτ (show τ.symm a < j from by change _ < (τ.symm a).val + 1; omega)
  have hright := hτ (show j < τ.symm b from by change (τ.symm a).val + 1 < _; omega)
  simp only [τ.apply_symm_apply] at hleft hright
  omega

private theorem arc_edge_parameter_image {n : ℕ} (p : Polygon E (n + 2))
    (j : Fin (n + 1)) :
    polygonLinearParameter p '' Icc (j.val : ℝ) ((j.val : ℝ) + 1) =
      segment ℝ (p j.castSucc) (p j.succ) := by
  have hj : polygonIntegerIndex (n + 2) (j.val : ℤ) = j.castSucc :=
    polygonIntegerIndex_nat j.castSucc
  have hnext : finRotate (n + 2) j.castSucc = j.succ := finRotate_of_lt j.isLt
  have heq (t : ℝ) (ht : t ∈ Icc (j.val : ℝ) ((j.val : ℝ) + 1)) :
      polygonLinearParameter p t =
        AffineMap.lineMap (p j.castSucc) (p j.succ) (t - j.val) := by
    simpa only [hj, Int.cast_natCast, Polygon.edgePath, hnext] using
      polygonLinearParameter_eq_edge p (j.val : ℤ)
        (by simpa only [Int.cast_natCast] using ht)
  rw [segment_eq_image_lineMap]
  apply Set.Subset.antisymm
  · rintro x ⟨t, ht, rfl⟩
    exact ⟨t - j.val, ⟨by linarith [ht.1], by linarith [ht.2]⟩, (heq t ht).symm⟩
  · rintro x ⟨t, ht, rfl⟩
    refine ⟨j.val + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [heq _ ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    congr 1
    ring

private theorem contact_gap_unit_endpoint {n m : ℕ}
    (c : Fin m ↪ Fin (n + 2)) (τ : Fin m ≃ Fin m)
    (hτ : StrictMono (fun j => (c (τ j)).val)) (j : Fin m)
    (w : Fin (n + 2)) (hw : w ∉ range c) :
    (w.val + 1 = (c (τ j)).val →
      (w.val : ℝ) ∈ polygonArcContactGap c τ j.castSucc) ∧
    ((c (τ j)).val + 1 = w.val →
      (w.val : ℝ) ∈ polygonArcContactGap c τ j.succ) := by
  have hne (i : Fin m) : (c (τ i)).val ≠ w.val := fun hh => hw ⟨τ i, Fin.ext hh⟩
  constructor
  · intro hstep
    simp only [polygonArcContactGap, Fin.val_castSucc, dif_pos j.isLt]
    refine ⟨?_, by change (w.val : ℝ) < (c (τ j)).val; exact_mod_cast (by omega)⟩
    by_cases hj : 0 < j.val
    · rw [dif_pos hj]
      have hlt := hτ (show (⟨j.val - 1, by omega⟩ : Fin m) < j from by
        change j.val - 1 < j.val; omega)
      dsimp only at hlt
      have hn := hne ⟨j.val - 1, by omega⟩
      change ((c (τ ⟨j.val - 1, by omega⟩)).val : ℝ) < w.val
      exact_mod_cast (show (c (τ ⟨j.val - 1, by omega⟩)).val < w.val from by omega)
    · rw [dif_neg hj]
      change (0 : ℝ) ≤ w.val
      exact Nat.cast_nonneg _
  · intro hstep
    change (w.val : ℝ) ∈ Ioi ((c (τ j)).val : ℝ) ∩
      (if hj : j.val + 1 < m then Iio ((c (τ ⟨j.val + 1, hj⟩)).val : ℝ)
        else Iic (n + 1 : ℕ))
    refine ⟨by change ((c (τ j)).val : ℝ) < w.val; exact_mod_cast (by omega), ?_⟩
    by_cases hj : j.val + 1 < m
    · rw [dif_pos hj]
      have hlt := hτ (show j < (⟨j.val + 1, hj⟩ : Fin m) from by
        change j.val < j.val + 1; omega)
      dsimp only at hlt
      have hn := hne ⟨j.val + 1, hj⟩
      change (w.val : ℝ) < (c (τ ⟨j.val + 1, hj⟩)).val
      exact_mod_cast (show w.val < (c (τ ⟨j.val + 1, hj⟩)).val from by omega)
    · rw [dif_neg hj]
      change (w.val : ℝ) ≤ (n + 1 : ℕ)
      exact_mod_cast (show w.val ≤ n + 1 from by omega)

variable [FiniteDimensional ℝ E]

private theorem terminal_gap_regions {n m : ℕ}
    {p : Polygon E (n + 2)} {r : Polygon E m}
    (hp : IsSimplePolygonalArc p) (hr : IsSimplePolygon r)
    (hdim : Module.finrank ℝ E = 2) (c : Fin m ↪ Fin (n + 2))
    (hc : ∀ i, r i = p (c i)) (hint : ∀ i, 0 < (c i).val ∧ (c i).val < n + 1)
    (a b : Fin m) (hab : (c a).val + 1 = (c b).val)
    (hcontact : r.boundary ℝ ∩ polygonArcBoundary p = range r ∪
      polygonLinearParameter p '' Icc ((c a).val : ℝ) ((c b).val : ℝ))
    (hfirst : p 0 ∈ polygonExterior r) (hlast : p (Fin.last (n + 1)) ∈ polygonExterior r) :
    ∃ τ : Fin m ≃ Fin m, StrictMono (fun j => (c (τ j)).val) ∧
      (τ.symm a).val + 1 = (τ.symm b).val ∧
      polygonLinearParameter p '' polygonArcContactGap c τ (τ.symm b).castSucc ⊆
        r.boundary ℝ ∧
      (∀ j : Fin (m + 1), j.val ≠ (τ.symm b).val →
        (polygonLinearParameter p '' polygonArcContactGap c τ j ⊆ polygonInterior r) ∨
        (polygonLinearParameter p '' polygonArcContactGap c τ j ⊆ polygonExterior r)) ∧
      polygonLinearParameter p '' polygonArcContactGap c τ 0 ⊆ polygonExterior r ∧
      polygonLinearParameter p '' polygonArcContactGap c τ (Fin.last m) ⊆ polygonExterior r := by
  have hm : 0 < m := by have := a.isLt; omega
  have hindex (i : Fin (n + 2)) : (i.val : ℝ) ∈ Icc (0 : ℝ) (n + 1 : ℕ) :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast (show i.val ≤ n + 1 from by omega)⟩
  have hdom {t : ℝ} (ht : t ∈ Icc ((c a).val : ℝ) ((c b).val : ℝ)) :
      t ∈ Icc (0 : ℝ) (n + 1 : ℕ) :=
    ⟨(hindex (c a)).1.trans ht.1, ht.2.trans (hindex (c b)).2⟩
  have htimes (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (n + 1 : ℕ)) :
      polygonLinearParameter p t ∈ r.boundary ℝ ↔
        (∃ i : Fin m, t = ((c i).val : ℝ)) ∨ t ∈ Icc ((c a).val : ℝ) ((c b).val : ℝ) := by
    constructor
    · intro hx
      have hg : polygonLinearParameter p t ∈ polygonArcBoundary p :=
        image_polygonLinearParameter_arc p ▸ ⟨t, ht, rfl⟩
      rcases (show polygonLinearParameter p t ∈ range r ∪
          polygonLinearParameter p '' Icc ((c a).val : ℝ) ((c b).val : ℝ) from
        hcontact ▸ ⟨hx, hg⟩) with ⟨i, hi⟩ | ⟨s, hs, hst⟩
      · exact Or.inl ⟨i, hp.injOn_polygonLinearParameter ht (hindex (c i))
          (hi.symm.trans ((hc i).trans (polygonLinearParameter_natVertex p (c i)).symm))⟩
      · exact Or.inr ((hp.injOn_polygonLinearParameter (hdom hs) ht hst) ▸ hs)
    · rintro (⟨i, rfl⟩ | hx)
      · rw [polygonLinearParameter_natVertex, ← hc i]
        exact polygon_vertex_mem_boundary r i
      · exact (show polygonLinearParameter p t ∈ r.boundary ℝ ∩ polygonArcBoundary p from
          hcontact.symm ▸ Or.inr ⟨t, hx, rfl⟩).1
  obtain ⟨τ, hτ⟩ := exists_sorted_contact_permutation c
  have hrank := sorted_adjacent_contact_ranks c τ hτ a b hab
  obtain ⟨hg, hg0, hgm, _⟩ := contact_gap_properties hm c τ hτ hint
  have hbpos : 0 < (τ.symm b).val := by omega
  have hpred : (⟨(τ.symm b).val - 1, by have := (τ.symm b).isLt; omega⟩ : Fin m) =
      τ.symm a := by apply Fin.ext; change (τ.symm b).val - 1 = _; omega
  have hshared : polygonArcContactGap c τ (τ.symm b).castSucc =
      Ioo ((c a).val : ℝ) ((c b).val : ℝ) := by
    simp only [polygonArcContactGap, Fin.val_castSucc, dif_pos hbpos,
      dif_pos (τ.symm b).isLt, hpred, τ.apply_symm_apply, Ioi_inter_Iio]
  have hsharedC : polygonLinearParameter p ''
      polygonArcContactGap c τ (τ.symm b).castSucc ⊆ r.boundary ℝ := by
    rw [hshared]
    rintro _ ⟨t, ht, rfl⟩
    exact (htimes t (hdom ⟨ht.1.le, ht.2.le⟩)).mpr (Or.inr ⟨ht.1.le, ht.2.le⟩)
  have hΓ : Continuous (polygonLinearParameter p) :=
    (continuous_polygonLinearParameter (p := fun _ : Unit => p)
      (fun _ => continuous_const)).comp
      ((continuous_const : Continuous (fun _ : ℝ => ())).prodMk continuous_id)
  obtain ⟨hI, hO, _, _, hdis, hcover, _⟩ := hr.polygonRegions_spec hdim
  have hlabel (j : Fin (m + 1)) (hj : j.val ≠ (τ.symm b).val) :
      (polygonLinearParameter p '' polygonArcContactGap c τ j ⊆ polygonInterior r) ∨
      (polygonLinearParameter p '' polygonArcContactGap c τ j ⊆ polygonExterior r) := by
    apply ((hg j).2.1.image _ hΓ.continuousOn).subset_or_subset hI hO hdis
    rw [hcover]
    rintro _ ⟨t, ht, rfl⟩ htC
    rcases (htimes t ((hg j).2.2.1 ht)).mp htC with ⟨i, hi⟩ | hi
    · exact (hg j).2.2.2 t ht i hi
    · by_cases hja : j.val ≤ (τ.symm a).val
      · have hjm : j.val < m := by have := (τ.symm a).isLt; omega
        have hle : ((c (τ ⟨j.val, hjm⟩)).val : ℝ) ≤ ((c a).val : ℝ) := by
          exact_mod_cast (show (c (τ ⟨j.val, hjm⟩)).val ≤ (c a).val from by
            simpa only [τ.apply_symm_apply] using hτ.monotone
              (show (⟨j.val, hjm⟩ : Fin m) ≤ τ.symm a from hja))
        simp only [polygonArcContactGap, dif_pos hjm] at ht
        exact (not_lt_of_ge (hle.trans hi.1)) ht.2
      · have hjpos : 0 < j.val := by omega
        have hle : ((c b).val : ℝ) ≤ ((c (τ ⟨j.val - 1, by omega⟩)).val : ℝ) := by
          exact_mod_cast (show (c b).val ≤ (c (τ ⟨j.val - 1, by omega⟩)).val from by
            simpa only [τ.apply_symm_apply] using hτ.monotone
              (show τ.symm b ≤ ⟨j.val - 1, by omega⟩ from by change _ ≤ j.val - 1; omega))
        simp only [polygonArcContactGap, dif_pos hjpos] at ht
        exact (not_lt_of_ge (hi.2.trans hle)) ht.1
  refine ⟨τ, hτ, hrank, hsharedC, hlabel, ?_, ?_⟩
  · rcases hlabel 0 (by simpa only [Fin.val_zero] using Nat.ne_of_lt hbpos) with h | h
    · have hx := h ⟨0, hg0, rfl⟩
      rw [show (0 : ℝ) = ((0 : Fin (n + 2)).val : ℝ) by simp,
        polygonLinearParameter_natVertex] at hx
      exact (Set.disjoint_left.mp hdis hx hfirst).elim
    · exact h
  · have hmlast : (Fin.last m).val ≠ (τ.symm b).val := ne_of_gt (τ.symm b).isLt
    rcases hlabel (Fin.last m) hmlast with h | h
    · have hx := h ⟨(n + 1 : ℕ), hgm, rfl⟩
      rw [show ((n + 1 : ℕ) : ℝ) = ((Fin.last (n + 1)).val : ℝ) by rfl,
        polygonLinearParameter_natVertex] at hx
      exact (Set.disjoint_left.mp hdis hx hlast).elim
    · exact h

set_option maxHeartbeats 800000 in

theorem IsSimplePolygonalArc.exists_terminal_inside_gaps {n k : ℕ}
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (hdim : Module.finrank ℝ E = 2) (hk : 2 ≤ k)
    (c : Fin (k + 1) ↪ Fin (n + 2))
    (hint : ∀ i, c i ≠ 0 ∧ c i ≠ Fin.last (n + 1))
    (hadj : c (Fin.last k) = (finRotate (n + 2)).symm (c 0) ∨
      c (Fin.last k) = finRotate (n + 2) (c 0))
    (hwnot : (if c (Fin.last k) = (finRotate (n + 2)).symm (c 0)
      then finRotate (n + 2) (c 0) else (finRotate (n + 2)).symm (c 0)) ∉ range c) :
    let r : Polygon E (k + 1) := ⟨fun i => p (c i)⟩
    let u := c 0
    let v := c (Fin.last k)
    let w := if v = (finRotate (n + 2)).symm u then finRotate (n + 2) u
      else (finRotate (n + 2)).symm u
    let z := if v = (finRotate (n + 2)).symm u then (finRotate (n + 2)).symm v
      else finRotate (n + 2) v
    let I := polygonInterior r
    let O := polygonExterior r
    let U := AffineMap.lineMap (p u) (p w) (1 / 2 : ℝ) ∈ I
    let V := AffineMap.lineMap (p v) (p z) (1 / 2 : ℝ) ∈ I
    IsSimplePolygon r →
    r.boundary ℝ ∩ polygonArcBoundary p = range r ∪ segment ℝ (p v) (p u) →
    p 0 ∈ O → p (Fin.last (n + 1)) ∈ O →
    (∀ i : Fin (k + 1), i ≠ 0 → i ≠ Fin.last k →
      ∃ ε : ℝ, 0 < ε ∧ ∃ W A B : Set E,
        IsOpen W ∧ r i ∈ W ∧ IsPreconnected A ∧ IsPreconnected B ∧
        A ∪ B = W \ r.boundary ℝ ∧
        (∀ t ∈ Ioo 0 ε, AffineMap.lineMap (r i)
          (p ((finRotate (n + 2)).symm (c i))) t ∈ A) ∧
        (∀ t ∈ Ioo 0 ε, AffineMap.lineMap (r i)
          (p (finRotate (n + 2) (c i))) t ∈ B)) →
    ∃ τ : Fin (k + 1) ≃ Fin (k + 1), ∃ B : Finset (Fin k),
      let J := fun j : Fin k => Ioo ((c (τ j.castSucc)).val : ℝ) ((c (τ j.succ)).val : ℝ)
      let K := fun j : Fin k => Icc ((c (τ j.castSucc)).val : ℝ) ((c (τ j.succ)).val : ℝ)
      StrictMono (fun j => (c (τ j)).val) ∧
      (∀ j, j ∈ B ↔ polygonLinearParameter p '' J j ⊆ I) ∧
      (∀ i : Fin (k + 1),
        ((i = 0 ∧ U) ∨ (i = Fin.last k ∧ V) ∨ (i ≠ 0 ∧ i ≠ Fin.last k)) ↔
          ∃ j : Fin k, j ∈ B ∧ (τ j.castSucc = i ∨ τ j.succ = i)) ∧
      (∀ i : Fin (k + 1), ∀ a ∈ B, ∀ b ∈ B,
        (τ a.castSucc = i ∨ τ a.succ = i) →
        (τ b.castSucc = i ∨ τ b.succ = i) → a = b) ∧
      (∀ j ∈ B, (polygonLinearParameter p '' K j) ∩ r.boundary ℝ =
        {r (τ j.castSucc), r (τ j.succ)}) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1,
        (AffineMap.lineMap (p u) (p w) t ∈ I ↔ U) ∧
        (AffineMap.lineMap (p u) (p w) t ∈ O ↔ ¬ U) ∧
        (AffineMap.lineMap (p v) (p z) t ∈ I ↔ V) ∧
        (AffineMap.lineMap (p v) (p z) t ∈ O ↔ ¬ V)) ∧
      (¬ U → p w ∈ O) ∧
      (∀ j ∈ B, (τ j.castSucc = 0 ∨ τ j.succ = 0) →
        p w ∈ polygonLinearParameter p '' J j) := by
  classical
  dsimp only
  intro hr hcontact hfirst hlast hcross
  let r : Polygon E (k + 1) := ⟨fun i => p (c i)⟩
  let u := c 0
  let v := c (Fin.last k)
  let w := if v = (finRotate (n + 2)).symm u then finRotate (n + 2) u
    else (finRotate (n + 2)).symm u
  let z := if v = (finRotate (n + 2)).symm u then (finRotate (n + 2)).symm v
    else finRotate (n + 2) v
  let a : Fin (k + 1) := if v = (finRotate (n + 2)).symm u then Fin.last k else 0
  let b : Fin (k + 1) := if v = (finRotate (n + 2)).symm u then 0 else Fin.last k
  have hintN (i : Fin (k + 1)) : 0 < (c i).val ∧ (c i).val < n + 1 :=
    ⟨Nat.pos_of_ne_zero (fun h => (hint i).1 (Fin.ext h)),
      Fin.lt_last_iff_ne_last.mpr (hint i).2⟩
  have hneighbor (i : Fin (k + 1)) :
      ((finRotate (n + 2)).symm (c i)).val + 1 = (c i).val ∧
      (c i).val + 1 = (finRotate (n + 2) (c i)).val := by
    obtain ⟨a, b, hai, hbi, hap, hbs, _⟩ :=
      exists_arc_incident_edge_indices (c i) (hint i).1 (hint i).2
    constructor
    · rw [← hap, ← hai]
      rfl
    · rw [← hbs, ← hbi]
      rfl
  have hab : (c a).val + 1 = (c b).val := by
    by_cases h : v = (finRotate (n + 2)).symm u
    · simp only [a, b, if_pos h]
      change v.val + 1 = u.val
      rw [h]
      exact (hneighbor 0).1
    · have hv : v = finRotate (n + 2) u := hadj.resolve_left h
      simp only [a, b, if_neg h]
      change u.val + 1 = v.val
      rw [hv]
      exact (hneighbor 0).2
  let e : Fin (n + 1) := ⟨(c a).val, by have := (hintN b).2; omega⟩
  have he0 : e.castSucc = c a := Fin.ext rfl
  have he1 : e.succ = c b := Fin.ext hab
  have hshared : segment ℝ (p v) (p u) = polygonLinearParameter p ''
      Icc ((c a).val : ℝ) ((c b).val : ℝ) := by
    have hv : ((c b).val : ℝ) = (e.val : ℝ) + 1 := by exact_mod_cast hab.symm
    rw [hv, show ((c a).val : ℝ) = (e.val : ℝ) by rfl, arc_edge_parameter_image, he0, he1]
    by_cases h : v = (finRotate (n + 2)).symm u
    · simp only [a, b, if_pos h]
      rfl
    · simp only [a, b, if_neg h]
      exact segment_symm ℝ _ _
  have hcontact' : r.boundary ℝ ∩ polygonArcBoundary p = range r ∪
      polygonLinearParameter p '' Icc ((c a).val : ℝ) ((c b).val : ℝ) := by
    rw [← hshared]
    exact hcontact
  obtain ⟨τ, hτ, hrank, hsharedC, hlabel, hfirstO, hlastO⟩ :=
    terminal_gap_regions hp hr hdim c (fun _ => rfl) hintN a b hab hcontact' hfirst hlast
  obtain ⟨hg, _, _, hsamples⟩ := contact_gap_properties (by omega) c τ hτ hintN
  let g := fun j : Fin (k + 2) => polygonLinearParameter p '' polygonArcContactGap c τ j
  let inside := fun j => g j ⊆ polygonInterior r
  let outside := fun j => g j ⊆ polygonExterior r
  let U := AffineMap.lineMap (p u) (p w) (1 / 2 : ℝ) ∈ polygonInterior r
  let V := AffineMap.lineMap (p v) (p z) (1 / 2 : ℝ) ∈ polygonInterior r
  let fu := if v = (finRotate (n + 2)).symm u then (τ.symm 0).succ else (τ.symm 0).castSucc
  let fv := if v = (finRotate (n + 2)).symm u
    then (τ.symm (Fin.last k)).castSucc else (τ.symm (Fin.last k)).succ
  have hdis := (hr.polygonRegions_spec hdim).2.2.2.2.1
  have hnotboth (j : Fin (k + 2)) : ¬ (inside j ∧ outside j) := by
    rintro ⟨hi, ho⟩
    obtain ⟨t, ht⟩ := (hg j).1
    exact Set.disjoint_left.mp hdis (hi ⟨t, ht, rfl⟩) (ho ⟨t, ht, rfl⟩)
  have hsharednot : ¬ inside (τ.symm b).castSucc := by
    intro hi
    obtain ⟨t, ht⟩ := (hg (τ.symm b).castSucc).1
    exact (hi ⟨t, ht, rfl⟩).1 (hsharedC ⟨t, ht, rfl⟩)
  have hforceI (j : Fin (k + 2)) {x : E} (hx : x ∈ g j)
      (hxI : x ∈ polygonInterior r) : inside j := by
    by_cases hj : j.val = (τ.symm b).val
    · have heq : j = (τ.symm b).castSucc := Fin.ext hj
      exact (hxI.1 (hsharedC (heq ▸ hx))).elim
    · rcases hlabel j hj with hi | ho
      · exact hi
      · exact (Set.disjoint_left.mp hdis hxI (ho hx)).elim
  have hforceO (j : Fin (k + 2)) {x : E} (hx : x ∈ g j)
      (hxO : x ∈ polygonExterior r) : outside j := by
    by_cases hj : j.val = (τ.symm b).val
    · have heq : j = (τ.symm b).castSucc := Fin.ext hj
      exact (hxO.1 (hsharedC (heq ▸ hx))).elim
    · rcases hlabel j hj with hi | ho
      · exact (Set.disjoint_left.mp hdis (hi hx) hxO).elim
      · exact ho
  have hfree : fu.val ≠ (τ.symm b).val ∧ fv.val ≠ (τ.symm b).val := by
    by_cases h : v = (finRotate (n + 2)).symm u
    · simp only [a, b, if_pos h] at hrank
      simp only [fu, fv, b, if_pos h, Fin.val_succ, Fin.val_castSucc]
      omega
    · simp only [a, b, if_neg h] at hrank
      simp only [fu, fv, b, if_neg h, Fin.val_succ, Fin.val_castSucc]
      omega
  have hrayU (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      AffineMap.lineMap (p u) (p w) t ∈ g fu := by
    have hs := hsamples (τ.symm 0) t ht
    simp only [τ.apply_symm_apply] at hs
    have heq := contact_parameter_neighbors p u (hint 0).1 (hint 0).2 ⟨ht.1.le, ht.2.le⟩
    by_cases h : v = (finRotate (n + 2)).symm u
    · exact ⟨u.val + t, by simpa only [fu, if_pos h] using hs.2,
        by simpa only [w, if_pos h] using heq.2⟩
    · exact ⟨u.val - t, by simpa only [fu, if_neg h] using hs.1,
        by simpa only [w, if_neg h] using heq.1⟩
  have hrayV (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      AffineMap.lineMap (p v) (p z) t ∈ g fv := by
    have hs := hsamples (τ.symm (Fin.last k)) t ht
    simp only [τ.apply_symm_apply] at hs
    have heq := contact_parameter_neighbors p v
      (hint (Fin.last k)).1 (hint (Fin.last k)).2 ⟨ht.1.le, ht.2.le⟩
    by_cases h : v = (finRotate (n + 2)).symm u
    · exact ⟨v.val - t, by simpa only [fv, if_pos h] using hs.1,
        by simpa only [z, if_pos h] using heq.1⟩
    · exact ⟨v.val + t, by simpa only [fv, if_neg h] using hs.2,
        by simpa only [z, if_neg h] using heq.2⟩
  have hU : inside fu ↔ U :=
    ⟨fun h => h (hrayU (1 / 2) (by constructor <;> norm_num)),
      fun h => hforceI fu (hrayU (1 / 2) (by constructor <;> norm_num)) h⟩
  have hV : inside fv ↔ V :=
    ⟨fun h => h (hrayV (1 / 2) (by constructor <;> norm_num)),
      fun h => hforceI fv (hrayV (1 / 2) (by constructor <;> norm_num)) h⟩
  have hrays (j : Fin (k + 2)) (A : Prop) (hj : j.val ≠ (τ.symm b).val)
      (hA : inside j ↔ A) {x : E} (hx : x ∈ g j) :
      (x ∈ polygonInterior r ↔ A) ∧ (x ∈ polygonExterior r ↔ ¬ A) := by
    refine ⟨⟨fun h => hA.mp (hforceI j hx h), fun h => hA.mpr h hx⟩, ?_⟩
    refine ⟨fun hxO h => Set.disjoint_left.mp hdis (hA.mpr h hx) hxO, ?_⟩
    intro hn
    exact ((hlabel j hj).resolve_left (fun hi => hn (hA.mp hi))) hx
  have hwhichU :
      ((τ.symm 0).castSucc = (τ.symm b).castSucc ∧ (τ.symm 0).succ = fu) ∨
      ((τ.symm 0).succ = (τ.symm b).castSucc ∧ (τ.symm 0).castSucc = fu) := by
    by_cases h : v = (finRotate (n + 2)).symm u
    · exact Or.inl ⟨by simp only [b, if_pos h], by simp only [fu, if_pos h]⟩
    · refine Or.inr ⟨?_, by simp only [fu, if_neg h]⟩
      apply Fin.ext
      simpa only [a, b, if_neg h, Fin.val_succ, Fin.val_castSucc] using hrank
  have hwhichV :
      ((τ.symm (Fin.last k)).castSucc = (τ.symm b).castSucc ∧
        (τ.symm (Fin.last k)).succ = fv) ∨
      ((τ.symm (Fin.last k)).succ = (τ.symm b).castSucc ∧
        (τ.symm (Fin.last k)).castSucc = fv) := by
    by_cases h : v = (finRotate (n + 2)).symm u
    · refine Or.inr ⟨?_, by simp only [fv, if_pos h]⟩
      apply Fin.ext
      simpa only [a, b, if_pos h, Fin.val_succ, Fin.val_castSucc] using hrank
    · exact Or.inl ⟨by simp only [b, if_neg h], by simp only [fv, if_neg h]⟩
  have hendpoint (i : Fin (k + 1)) (f : Fin (k + 2)) (P : Prop)
      (hP : inside f ↔ P)
      (hw : ((τ.symm i).castSucc = (τ.symm b).castSucc ∧ (τ.symm i).succ = f) ∨
        ((τ.symm i).succ = (τ.symm b).castSucc ∧ (τ.symm i).castSucc = f)) :
      ((inside (τ.symm i).castSucc ∨ inside (τ.symm i).succ) ↔ P) ∧
      ¬ (inside (τ.symm i).castSucc ∧ inside (τ.symm i).succ) := by
    rcases hw with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [hl, hr]
      simpa only [hsharednot, false_or, false_and, not_false_eq_true, and_true] using hP
    · rw [hl, hr]
      simpa only [hsharednot, or_false, and_false, not_false_eq_true, and_true] using hP
  let Active := fun i : Fin (k + 1) =>
    (i = 0 ∧ U) ∨ (i = Fin.last k ∧ V) ∨ (i ≠ 0 ∧ i ≠ Fin.last k)
  have hzeroLast : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  have hinc (i : Fin (k + 1)) :
      ((inside (τ.symm i).castSucc ∨ inside (τ.symm i).succ) ↔ Active i) ∧
      ¬ (inside (τ.symm i).castSucc ∧ inside (τ.symm i).succ) := by
    by_cases hi0 : i = 0
    · subst i
      simpa only [Active, ne_eq, eq_self_iff_true, true_and, hzeroLast, false_and,
        not_true_eq_false, false_or, or_false] using hendpoint 0 fu U hU hwhichU
    by_cases hil : i = Fin.last k
    · subst i
      simpa only [Active, ne_eq, eq_self_iff_true, hzeroLast.symm, false_and, true_and,
        not_true_eq_false, and_false, false_or, or_false] using
          hendpoint (Fin.last k) fv V hV hwhichV
    obtain ⟨ε, hε, W, A, D, hW, hiW, hA, hD, hlocal, hleft, hright⟩ :=
      hcross i hi0 hil
    have hregions := hr.opposite_local_rays_regions hdim (r i)
      (p ((finRotate (n + 2)).symm (c i))) (p (finRotate (n + 2) (c i)))
      ε W A D (polygon_vertex_mem_boundary r i) hε hW hiW hA hD hlocal hleft hright
    let s := min ε 1 / 2
    have hs0 : 0 < s := div_pos (lt_min hε zero_lt_one) (by norm_num)
    have hsε : s < ε := by dsimp only [s] at hs0 ⊢; linarith [min_le_left ε (1 : ℝ)]
    have hs1 : s < 1 := by dsimp only [s] at hs0 ⊢; linarith [min_le_right ε (1 : ℝ)]
    have hs := hsamples (τ.symm i) s ⟨hs0, hs1⟩
    simp only [τ.apply_symm_apply] at hs
    have hvalues := contact_parameter_neighbors p (c i) (hint i).1 (hint i).2
      ⟨hs0.le, hs1.le⟩
    have hL : AffineMap.lineMap (r i) (p ((finRotate (n + 2)).symm (c i))) s ∈
        g (τ.symm i).castSucc := ⟨(c i).val - s, hs.1, hvalues.1⟩
    have hR : AffineMap.lineMap (r i) (p (finRotate (n + 2) (c i))) s ∈
        g (τ.symm i).succ := ⟨(c i).val + s, hs.2, hvalues.2⟩
    have hlabels : (inside (τ.symm i).castSucc ∧ outside (τ.symm i).succ) ∨
        (outside (τ.symm i).castSucc ∧ inside (τ.symm i).succ) := by
      rcases hregions with ⟨hI, hO⟩ | ⟨hO, hI⟩
      · exact Or.inl ⟨hforceI _ hL (hI s ⟨hs0, hsε⟩), hforceO _ hR (hO s ⟨hs0, hsε⟩)⟩
      · exact Or.inr ⟨hforceO _ hL (hO s ⟨hs0, hsε⟩), hforceI _ hR (hI s ⟨hs0, hsε⟩)⟩
    have hactive : Active i := Or.inr (Or.inr ⟨hi0, hil⟩)
    rcases hlabels with ⟨hI, hO⟩ | ⟨hO, hI⟩
    · exact ⟨⟨fun _ => hactive, fun _ => Or.inl hI⟩,
        fun h => hnotboth _ ⟨h.2, hO⟩⟩
    · exact ⟨⟨fun _ => hactive, fun _ => Or.inr hI⟩,
        fun h => hnotboth _ ⟨h.1, hO⟩⟩
  have hmid (j : Fin k) : polygonArcContactGap c τ j.succ.castSucc =
      Ioo ((c (τ j.castSucc)).val : ℝ) ((c (τ j.succ)).val : ℝ) := by
    simp only [polygonArcContactGap, Fin.val_castSucc, Fin.val_succ,
      Nat.zero_lt_succ, dif_pos, Nat.add_sub_cancel]
    rw [dif_pos (show j.val + 1 < k + 1 from Nat.add_lt_add_right j.isLt 1)]
    rfl
  let B : Finset (Fin k) := Finset.univ.filter (fun j => inside j.succ.castSucc)
  have hB (j : Fin k) : j ∈ B ↔ inside j.succ.castSucc := by simp only [B,
    Finset.mem_filter, Finset.mem_univ, true_and]
  have houter : ¬ inside 0 ∧ ¬ inside (Fin.last (k + 1)) :=
    ⟨fun h => hnotboth _ ⟨h, hfirstO⟩, fun h => hnotboth _ ⟨h, hlastO⟩⟩
  have hend (i : Fin (k + 1)) (j : Fin k)
      (hji : τ j.castSucc = i ∨ τ j.succ = i) :
      j.succ.castSucc = (τ.symm i).succ ∨ j.succ.castSucc = (τ.symm i).castSucc := by
    rcases hji with rfl | rfl
    · exact Or.inl (by simp only [τ.symm_apply_apply]; rfl)
    · exact Or.inr (by simp only [τ.symm_apply_apply])
  have hcover (i : Fin (k + 1)) :
      Active i ↔ ∃ j : Fin k, j ∈ B ∧ (τ j.castSucc = i ∨ τ j.succ = i) := by
    constructor
    · intro hi
      rcases (hinc i).1.mpr hi with hl | hr
      · have hpos : 0 < (τ.symm i).val := by
          by_contra hn
          have heq : (τ.symm i).castSucc = 0 := Fin.ext
            (by change (τ.symm i).val = 0; omega)
          exact houter.1 (heq ▸ hl)
        let j : Fin k := ⟨(τ.symm i).val - 1, by have := (τ.symm i).isLt; omega⟩
        have heq : j.succ = τ.symm i := by apply Fin.ext; change _ - 1 + 1 = _; omega
        refine ⟨j, (hB j).mpr ?_, Or.inr ?_⟩
        · simpa only [heq] using hl
        · rw [heq, τ.apply_symm_apply]
      · have hlt : (τ.symm i).val < k := by
          by_contra hn
          have heq : (τ.symm i).succ = Fin.last (k + 1) := by
            apply Fin.ext
            change (τ.symm i).val + 1 = k + 1
            have := (τ.symm i).isLt
            omega
          exact houter.2 (heq ▸ hr)
        let j : Fin k := ⟨(τ.symm i).val, hlt⟩
        have heq : j.castSucc = τ.symm i := Fin.ext rfl
        refine ⟨j, (hB j).mpr ?_, Or.inl ?_⟩
        · have hj : j.succ.castSucc = (τ.symm i).succ := Fin.ext rfl
          exact hj.symm ▸ hr
        · rw [heq, τ.apply_symm_apply]
    · rintro ⟨j, hj, he⟩
      rcases hend i j he with h | h
      · exact (hinc i).1.mp (Or.inr (h ▸ (hB j).mp hj))
      · exact (hinc i).1.mp (Or.inl (h ▸ (hB j).mp hj))
  have hunique (i : Fin (k + 1)) (j : Fin k) (hj : j ∈ B) (l : Fin k)
      (hl : l ∈ B) (hji : τ j.castSucc = i ∨ τ j.succ = i)
      (hli : τ l.castSucc = i ∨ τ l.succ = i) : j = l := by
    have hjI := (hB j).mp hj
    have hlI := (hB l).mp hl
    rcases hend i j hji with he | he <;> rcases hend i l hli with hf | hf
    · apply Fin.ext; have hv := congrArg Fin.val (he.trans hf.symm); simpa using hv
    · exact ((hinc i).2 ⟨hf ▸ hlI, he ▸ hjI⟩).elim
    · exact ((hinc i).2 ⟨he ▸ hjI, hf ▸ hlI⟩).elim
    · apply Fin.ext; have hv := congrArg Fin.val (he.trans hf.symm); simpa using hv
  have hclosed (j : Fin k) (hj : j ∈ B) :
      (polygonLinearParameter p '' Icc ((c (τ j.castSucc)).val : ℝ)
        ((c (τ j.succ)).val : ℝ)) ∩ r.boundary ℝ =
        {r (τ j.castSucc), r (τ j.succ)} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxC⟩
      by_cases hl : t = ((c (τ j.castSucc)).val : ℝ)
      · rw [hl, polygonLinearParameter_natVertex]; exact Or.inl rfl
      by_cases hr : t = ((c (τ j.succ)).val : ℝ)
      · rw [hr, polygonLinearParameter_natVertex]; exact Or.inr rfl
      have htJ : t ∈ polygonArcContactGap c τ j.succ.castSucc := by
        rw [hmid]; exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hl), lt_of_le_of_ne ht.2 hr⟩
      exact (((hB j).mp hj ⟨t, htJ, rfl⟩).1 hxC).elim
    · have hle : ((c (τ j.castSucc)).val : ℝ) ≤ ((c (τ j.succ)).val : ℝ) := by
        exact_mod_cast (hτ (show j.castSucc < j.succ from by change j.val < j.val + 1; omega)).le
      rintro (rfl | rfl)
      · exact ⟨⟨_, ⟨le_rfl, hle⟩, polygonLinearParameter_natVertex p _⟩,
          polygon_vertex_mem_boundary r _⟩
      · exact ⟨⟨_, ⟨hle, le_rfl⟩, polygonLinearParameter_natVertex p _⟩,
          polygon_vertex_mem_boundary r _⟩
  have hwg : p w ∈ g fu := by
    have hw := contact_gap_unit_endpoint c τ hτ (τ.symm 0) w hwnot
    simp only [τ.apply_symm_apply] at hw
    refine ⟨w.val, ?_, polygonLinearParameter_natVertex p w⟩
    by_cases h : v = (finRotate (n + 2)).symm u
    · simpa only [fu, if_pos h] using hw.2
        (by simpa only [w, if_pos h] using (hneighbor 0).2)
    · simpa only [fu, if_neg h] using hw.1
        (by simpa only [w, if_neg h] using (hneighbor 0).1)
  refine ⟨τ, B, hτ, ?_, hcover, hunique, hclosed, ?_, ?_, ?_⟩
  · intro j
    simpa only [inside, g, hmid] using hB j
  · intro t ht
    exact ⟨(hrays fu U hfree.1 hU (hrayU t ht)).1,
      (hrays fu U hfree.1 hU (hrayU t ht)).2,
      (hrays fv V hfree.2 hV (hrayV t ht)).1,
      (hrays fv V hfree.2 hV (hrayV t ht)).2⟩
  · intro hU'
    exact (hrays fu U hfree.1 hU hwg).2.mpr hU'
  · intro j hj he
    have hjI := (hB j).mp hj
    have heq : j.succ.castSucc = fu := by
      rcases hend 0 j he with he | he <;>
        rcases hwhichU with ⟨hs, hf⟩ | ⟨hs, hf⟩
      · exact he.trans hf
      · exact (hsharednot ((he.trans hs) ▸ hjI)).elim
      · exact (hsharednot ((he.trans hs) ▸ hjI)).elim
      · exact he.trans hf
    change p w ∈ polygonLinearParameter p '' _
    rw [← hmid, heq]
    exact hwg

end PoincareConjecture.M25.Topology3D
