import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcInsideGaps
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcSubarc
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.Crosscut
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.NoninterlacingMatching
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Group.Nat.Even

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

private theorem rank_bit_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  have hb : b.val = 0 ∨ b.val = 1 := by omega
  exact hb.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))

private theorem exists_actual_rank_pairing {m : ℕ} (heven : Even m) (hfour : 4 ≤ m)
    (σ : Fin m ≃ Fin m) :
    ∃ h : ℕ, 2 ≤ h ∧ ∃ ι : Fin h × Fin 2 ≃ Fin m,
      (∀ a b, (σ.symm (ι (a, b))).val = b.val + 2 * a.val) ∧
      ∃ M : Fin m → Fin m, Function.Involutive M ∧ (∀ i, M i ≠ i) ∧
        (∀ a b, M (ι (a, b)) = ι (a, Equiv.swap 0 1 b)) ∧
        (∀ i j, j ≠ i → j ≠ M i → (ι.symm i).1 ≠ (ι.symm j).1) := by
  obtain ⟨h, hh⟩ := heven
  have hm : m = h * 2 := by omega
  clear hh
  subst m
  let ι : Fin h × Fin 2 ≃ Fin (h * 2) := finProdFinEquiv.trans σ
  let S : Fin h × Fin 2 ≃ Fin h × Fin 2 :=
    Equiv.prodCongr (Equiv.refl (Fin h)) (Equiv.swap 0 1)
  let M : Fin (h * 2) → Fin (h * 2) := fun i => ι (S (ι.symm i))
  have hcoord (a : Fin h) (b : Fin 2) :
      (σ.symm (ι (a, b))).val = b.val + 2 * a.val := by
    change (σ.symm (σ (finProdFinEquiv (a, b)))).val = _
    rw [σ.symm_apply_apply]
    rfl
  have hS (x : Fin h × Fin 2) : S (S x) = x := by
    obtain ⟨a, b⟩ := x
    change (a, Equiv.swap 0 1 (Equiv.swap 0 1 b)) = (a, b)
    rw [Equiv.swap_apply_self]
  have hM : Function.Involutive M := by
    intro i
    dsimp only [M]
    rw [ι.symm_apply_apply, hS, ι.apply_symm_apply]
  have hmate (a : Fin h) (b : Fin 2) : M (ι (a, b)) = ι (a, Equiv.swap 0 1 b) := by
    dsimp only [M]
    rw [ι.symm_apply_apply]
    rfl
  have hne (i : Fin (h * 2)) : M i ≠ i := by
    intro heq
    have heq' : S (ι.symm i) = ι.symm i :=
      ι.injective (heq.trans (ι.apply_symm_apply i).symm)
    have hb := congrArg Prod.snd heq'
    change Equiv.swap 0 1 (ι.symm i).2 = (ι.symm i).2 at hb
    rcases rank_bit_cases (ι.symm i).2 with h0 | h1
    · rw [h0, Equiv.swap_apply_left] at hb
      have := congrArg Fin.val hb
      omega
    · rw [h1, Equiv.swap_apply_right] at hb
      have := congrArg Fin.val hb
      omega
  refine ⟨h, by omega, ι, hcoord, M, hM, hne, hmate, ?_⟩
  intro i j hji hjM heq
  obtain ⟨⟨a, b⟩, rfl⟩ := ι.surjective i
  obtain ⟨⟨a', b'⟩, rfl⟩ := ι.surjective j
  simp only [ι.symm_apply_apply] at heq
  change a = a' at heq
  subst a'
  rcases rank_bit_cases b with rfl | rfl <;> rcases rank_bit_cases b' with rfl | rfl
  · exact hji rfl
  · exact hjM (by simpa only [Equiv.swap_apply_left] using (hmate a 0).symm)
  · exact hjM (by simpa only [Equiv.swap_apply_right] using (hmate a 1).symm)
  · exact hji rfl

private theorem rank_pair_orientation {h m : ℕ} (ι : Fin h × Fin 2 ≃ Fin m)
    (M : Fin m → Fin m)
    (hmate : ∀ a b, M (ι (a, b)) = ι (a, Equiv.swap 0 1 b)) (i : Fin m) :
    (i = ι ((ι.symm i).1, 0) ∧ M i = ι ((ι.symm i).1, 1)) ∨
      (i = ι ((ι.symm i).1, 1) ∧ M i = ι ((ι.symm i).1, 0)) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := ι.surjective i
  simp only [ι.symm_apply_apply]
  rcases rank_bit_cases b with rfl | rfl
  · exact Or.inl ⟨rfl, by simpa only [Equiv.swap_apply_left] using hmate a 0⟩
  · exact Or.inr ⟨rfl, by simpa only [Equiv.swap_apply_right] using hmate a 1⟩

private theorem rank_pair_bounds {h m : ℕ} (σ : Fin m ≃ Fin m)
    (ι : Fin h × Fin 2 ≃ Fin m)
    (hcoord : ∀ a b, (σ.symm (ι (a, b))).val = b.val + 2 * a.val)
    (M : Fin m → Fin m)
    (hmate : ∀ a b, M (ι (a, b)) = ι (a, Equiv.swap 0 1 b)) (i : Fin m) :
    min (σ.symm i).val (σ.symm (M i)).val = 2 * (ι.symm i).1.val ∧
      max (σ.symm i).val (σ.symm (M i)).val = 2 * (ι.symm i).1.val + 1 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := ι.surjective i
  rw [hmate]
  simp only [ι.symm_apply_apply]
  rcases rank_bit_cases b with rfl | rfl
  · simp only [Equiv.swap_apply_left, hcoord, Fin.val_zero, Fin.val_one, zero_add]
    omega
  · simp only [Equiv.swap_apply_right, hcoord, Fin.val_zero, Fin.val_one, zero_add]
    omega

private theorem rank_pair_separation {h m : ℕ} (σ : Fin m ≃ Fin m)
    (ι : Fin h × Fin 2 ≃ Fin m)
    (hcoord : ∀ a b, (σ.symm (ι (a, b))).val = b.val + 2 * a.val)
    (M : Fin m → Fin m)
    (hmate : ∀ a b, M (ι (a, b)) = ι (a, Equiv.swap 0 1 b))
    (i j : Fin m) (hne : (ι.symm i).1 ≠ (ι.symm j).1) :
    max (σ.symm i).val (σ.symm (M i)).val <
        min (σ.symm j).val (σ.symm (M j)).val ∨
      max (σ.symm j).val (σ.symm (M j)).val <
        min (σ.symm i).val (σ.symm (M i)).val := by
  obtain ⟨himin, himax⟩ := rank_pair_bounds σ ι hcoord M hmate i
  obtain ⟨hjmin, hjmax⟩ := rank_pair_bounds σ ι hcoord M hmate j
  rw [himin, himax, hjmin, hjmax]
  have hvals : (ι.symm i).1.val ≠ (ι.symm j).1.val := fun heq => hne (Fin.ext heq)
  omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem rank_pair_open_image_subset {n m h : ℕ} (p : Polygon E (n + 2))
    (c : Fin m ↪ Fin (n + 2)) (σ : Fin m ≃ Fin m)
    (hσ : StrictMono (fun j => (c (σ j)).val)) (ι : Fin h × Fin 2 ≃ Fin m)
    (hcoord : ∀ a b, (σ.symm (ι (a, b))).val = b.val + 2 * a.val)
    (M : Fin m → Fin m)
    (hmate : ∀ a b, M (ι (a, b)) = ι (a, Equiv.swap 0 1 b))
    (S : Set E)
    (hgap : ∀ j : Fin (m + 1), ¬ Even j.val →
      polygonLinearParameter p '' polygonArcContactGap c σ j ⊆ S) (i : Fin m) :
    polygonLinearParameter p '' Ioo
      (min ((c i).val : ℝ) ((c (M i)).val : ℝ))
      (max ((c i).val : ℝ) ((c (M i)).val : ℝ)) ⊆ S := by
  have hpair (a : Fin h) : polygonLinearParameter p ''
      Ioo ((c (ι (a, 0))).val : ℝ) ((c (ι (a, 1))).val : ℝ) ⊆ S := by
    let lo := σ.symm (ι (a, 0))
    let hi := σ.symm (ι (a, 1))
    have hlo : lo.val = 2 * a.val := by
      simpa only [lo, Fin.val_zero, zero_add] using hcoord a 0
    have hhi : hi.val = 1 + 2 * a.val := by simpa only [hi, Fin.val_one] using hcoord a 1
    have hpos : 0 < hi.val := by omega
    have hpred : (⟨hi.val - 1, by omega⟩ : Fin m) = lo := by
      apply Fin.ext
      change hi.val - 1 = lo.val
      omega
    have hset : polygonArcContactGap c σ hi.castSucc =
        Ioo ((c (ι (a, 0))).val : ℝ) ((c (ι (a, 1))).val : ℝ) := by
      simp only [polygonArcContactGap, Fin.val_castSucc, dif_pos hpos, dif_pos hi.isLt]
      rw [hpred]
      simp only [lo, hi, σ.apply_symm_apply, Ioi_inter_Iio]
    rw [← hset]
    apply hgap
    rw [Fin.val_castSucc, hhi, Nat.even_iff]
    omega
  obtain ⟨⟨a, b⟩, rfl⟩ := ι.surjective i
  have hlt : (c (ι (a, 0))).val < (c (ι (a, 1))).val := by
    simpa only [σ.apply_symm_apply] using hσ (show
      σ.symm (ι (a, 0)) < σ.symm (ι (a, 1)) from by
      simp only [Fin.lt_def, hcoord, Fin.val_zero, Fin.val_one]
      omega)
  have hle : ((c (ι (a, 0))).val : ℝ) ≤ ((c (ι (a, 1))).val : ℝ) := by
    exact_mod_cast hlt.le
  rcases rank_bit_cases b with rfl | rfl
  · simpa only [hmate, Equiv.swap_apply_left, min_eq_left hle, max_eq_right hle] using
      hpair a
  · simpa only [hmate, Equiv.swap_apply_right, min_eq_right hle, max_eq_left hle] using
      hpair a

private theorem subarc_rescaled_parameter {n k : ℕ} (p : Polygon E (n + 2))
    (q : Polygon E (k + 2)) (a b : Fin (n + 2))
    (hk : k + 1 = Nat.dist a.val b.val)
    (hparam : ∀ t ∈ Icc (0 : ℝ) (k + 1 : ℕ), polygonLinearParameter q t =
      polygonLinearParameter p (if a < b then (a.val : ℝ) + t else (a.val : ℝ) - t))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    polygonLinearParameter q (((k + 1 : ℕ) : ℝ) * t) =
      polygonLinearParameter p (AffineMap.lineMap (a.val : ℝ) (b.val : ℝ) t) := by
  have hk0 : (0 : ℝ) ≤ (k + 1 : ℕ) := Nat.cast_nonneg _
  rw [hparam _ ⟨mul_nonneg hk0 ht.1, (mul_le_mul_of_nonneg_left ht.2 hk0).trans_eq
    (mul_one _)⟩]
  congr 1
  rw [AffineMap.lineMap_apply_ring]
  by_cases hab : a < b
  · rw [if_pos hab]
    have hnat : a.val + (k + 1) = b.val := by
      rw [Nat.dist_eq_sub_of_le hab.le] at hk
      omega
    have hreal : (a.val : ℝ) + (k + 1 : ℕ) = b.val := by exact_mod_cast hnat
    rw [← hreal]
    ring
  · rw [if_neg hab]
    have hnat : b.val + (k + 1) = a.val := by
      rw [Nat.dist_eq_sub_of_le_right (le_of_not_gt hab)] at hk
      omega
    have hreal : (b.val : ℝ) + (k + 1 : ℕ) = a.val := by exact_mod_cast hnat
    rw [← hreal]
    ring

variable [FiniteDimensional ℝ E]

theorem IsSimplePolygonalArc.exists_inside_noninterlacing_matching {n m : ℕ}
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
    ∃ M : Fin m → Fin m,
      let T := fun i => polygonLinearParameter p '' Icc
        (min ((c i).val : ℝ) ((c (M i)).val : ℝ))
        (max ((c i).val : ℝ) ((c (M i)).val : ℝ))
      let S := fun i => polygonLinearParameter p '' Ioo
        (min ((c i).val : ℝ) ((c (M i)).val : ℝ))
        (max ((c i).val : ℝ) ((c (M i)).val : ℝ))
      let γ := fun (i : Fin m) (t : ℝ) => polygonLinearParameter p
        (AffineMap.lineMap ((c i).val : ℝ) ((c (M i)).val : ℝ) t)
      IsNoninterlacingMatching M ∧ Even m ∧ 4 ≤ m ∧
      (∀ i, S i ⊆ polygonInterior r ∧ T i ∩ r.boundary ℝ = {r i, r (M i)}) ∧
      (∀ i, ∃ k : ℕ, ∃ q : Polygon E (k + 2),
        k + 1 = Nat.dist (c i).val (c (M i)).val ∧ IsSimplePolygonalArc q ∧
        q 0 = r i ∧ q (Fin.last (k + 1)) = r (M i) ∧
        (∀ j : Fin (k + 2), q j = polygonLinearParameter p
          (if c i < c (M i) then ((c i).val : ℝ) + j.val else ((c i).val : ℝ) - j.val)) ∧
        polygonArcBoundary q = T i ∧
        polygonArcBoundary q \ {r i, r (M i)} = S i ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          polygonLinearParameter q (((k + 1 : ℕ) : ℝ) * t) = γ i t)) ∧
      (∀ i j, j ≠ i → j ≠ M i → Disjoint (T i) (T j)) ∧
      (∀ i, T (M i) = T i ∧ S (M i) = S i) ∧
      (∀ i t, γ (M i) t = γ i (1 - t)) := by
  classical
  obtain ⟨σ, hσ, heven, hfour, _, _, _, hgap, _, _, _⟩ :=
    hp.exists_alternating_contact_gaps hr hdim c hc hint hcontact hfirst hlast hcross
  obtain ⟨h, _, ι, hcoord, M, hM, hne, hmate, hkeys⟩ :=
    exists_actual_rank_pairing heven hfour σ
  let T := fun i => polygonLinearParameter p '' Icc
    (min ((c i).val : ℝ) ((c (M i)).val : ℝ))
    (max ((c i).val : ℝ) ((c (M i)).val : ℝ))
  let S := fun i => polygonLinearParameter p '' Ioo
    (min ((c i).val : ℝ) ((c (M i)).val : ℝ))
    (max ((c i).val : ℝ) ((c (M i)).val : ℝ))
  let γ := fun (i : Fin m) (t : ℝ) => polygonLinearParameter p
    (AffineMap.lineMap ((c i).val : ℝ) ((c (M i)).val : ℝ) t)
  have hopen (i : Fin m) : S i ⊆ polygonInterior r :=
    rank_pair_open_image_subset p c σ hσ ι hcoord M hmate (polygonInterior r)
      (fun j hj => (hgap j).2.2.2.2.2 hj) i
  have hci (i : Fin m) : c i ≠ c (M i) := fun hh => hne i (c.injective hh).symm
  have hq (i : Fin m) : ∃ k : ℕ, ∃ q : Polygon E (k + 2),
      k + 1 = Nat.dist (c i).val (c (M i)).val ∧ IsSimplePolygonalArc q ∧
      q 0 = r i ∧ q (Fin.last (k + 1)) = r (M i) ∧
      (∀ j : Fin (k + 2), q j = polygonLinearParameter p
        (if c i < c (M i) then ((c i).val : ℝ) + j.val else ((c i).val : ℝ) - j.val)) ∧
      polygonArcBoundary q = T i ∧ polygonArcBoundary q \ {r i, r (M i)} = S i ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        polygonLinearParameter q (((k + 1 : ℕ) : ℝ) * t) = γ i t) := by
    obtain ⟨k, q, hk, hs, hq0, hq1, hv, ht, hB, hS⟩ :=
      hp.exists_consecutive_subarc (c i) (c (M i)) (hci i)
    refine ⟨k, q, hk, hs, hq0.trans (hc i).symm, hq1.trans (hc (M i)).symm,
      hv, hB, ?_, ?_⟩
    · simpa only [← hc i, ← hc (M i)] using hS
    · exact fun t ht' => subarc_rescaled_parameter p q (c i) (c (M i)) hk ht t ht'
  have hincidence (i : Fin m) : T i ∩ r.boundary ℝ = {r i, r (M i)} := by
    obtain ⟨k, q, _, _, _, _, _, hB, hS, _⟩ := hq i
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hn
      have hxS : x ∈ S i := hS ▸ ⟨hB.symm ▸ hx.1, hn⟩
      exact (hopen i hxS).1 hx.2
    · rintro x (rfl | rfl)
      · refine ⟨⟨(c i).val, ⟨min_le_left _ _, le_max_left _ _⟩, ?_⟩,
          polygon_vertex_mem_boundary r i⟩
        exact (polygonLinearParameter_natVertex p (c i)).trans (hc i).symm
      · refine ⟨⟨(c (M i)).val, ⟨min_le_right _ _, le_max_right _ _⟩, ?_⟩,
          polygon_vertex_mem_boundary r (M i)⟩
        exact (polygonLinearParameter_natVertex p (c (M i))).trans (hc (M i)).symm
  have hindex (i : Fin (n + 2)) : (i.val : ℝ) ∈ Icc (0 : ℝ) (n + 1 : ℕ) :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast (show i.val ≤ n + 1 from by omega)⟩
  have hdom (i : Fin m) {t : ℝ}
      (ht : t ∈ Icc (min ((c i).val : ℝ) ((c (M i)).val : ℝ))
        (max ((c i).val : ℝ) ((c (M i)).val : ℝ))) :
      t ∈ Icc (0 : ℝ) (n + 1 : ℕ) :=
    ⟨(le_min (hindex (c i)).1 (hindex (c (M i))).1).trans ht.1,
      ht.2.trans (max_le (hindex (c i)).2 (hindex (c (M i))).2)⟩
  have horder (i j : Fin m)
      (hs : max (σ.symm i).val (σ.symm (M i)).val <
        min (σ.symm j).val (σ.symm (M j)).val) :
      max ((c i).val : ℝ) ((c (M i)).val : ℝ) <
        min ((c j).val : ℝ) ((c (M j)).val : ℝ) := by
    have hlt (a b : Fin m) (hab : (σ.symm a).val < (σ.symm b).val) :
        ((c a).val : ℝ) < ((c b).val : ℝ) := by
      exact_mod_cast (show (c a).val < (c b).val from by
        simpa only [σ.apply_symm_apply] using hσ hab)
    exact max_lt_iff.mpr ⟨lt_min (hlt i j (by omega)) (hlt i (M j) (by omega)),
      lt_min (hlt (M i) j (by omega)) (hlt (M i) (M j) (by omega))⟩
  have hdis (i j : Fin m) (hji : j ≠ i) (hjM : j ≠ M i) : Disjoint (T i) (T j) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
    have huv := hp.injOn_polygonLinearParameter (hdom i hu) (hdom j hv) hvu.symm
    subst v
    rcases rank_pair_separation σ ι hcoord M hmate i j (hkeys i j hji hjM) with hs | hs
    · have ho := horder i j hs
      exact (not_lt_of_ge (hv.1.trans hu.2)) ho
    · have ho := horder j i hs
      exact (not_lt_of_ge (hu.1.trans hv.2)) ho
  have hcurve (i : Fin m) : γ i '' Ioo (0 : ℝ) 1 ⊆ S i := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨AffineMap.lineMap ((c i).val : ℝ) ((c (M i)).val : ℝ) t, ?_, rfl⟩
    have hv : (c i).val ≠ (c (M i)).val := fun hh => hci i (Fin.ext hh)
    have hrne : ((c i).val : ℝ) ≠ ((c (M i)).val : ℝ) := by exact_mod_cast hv
    rcases lt_or_gt_of_ne hrne with hab | hba
    · simp only [min_eq_left hab.le, max_eq_right hab.le, mem_Ioo,
        AffineMap.lineMap_apply_ring]
      constructor <;> nlinarith [mul_pos (sub_pos.mpr hab) ht.1,
        mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht.2)]
    · simp only [min_eq_right hba.le, max_eq_left hba.le, mem_Ioo,
        AffineMap.lineMap_apply_ring]
      constructor <;> nlinarith [mul_pos (sub_pos.mpr hba) ht.1,
        mul_pos (sub_pos.mpr hba) (sub_pos.mpr ht.2)]
  have hΓ : Continuous (polygonLinearParameter p) :=
    (continuous_polygonLinearParameter (p := fun _ : Unit => p)
      (fun _ => continuous_const)).comp
      ((continuous_const : Continuous (fun _ : ℝ => ())).prodMk continuous_id)
  have hnon : IsNoninterlacingMatching M := by
    refine ⟨hM, hne, ?_⟩
    intro a b hab hbMa hMaMb
    obtain ⟨k, q, _, hs, hq0, hq1, _, hB, hS, _⟩ := hq a
    have hdist (x : Fin m) (hx : a ≤ x) :
        cyclicDistance a x = x.val - a.val := Fin.sub_val_of_le hx
    have hf0 : γ b 0 = r b := by
      simp only [γ, AffineMap.lineMap_apply_zero, polygonLinearParameter_natVertex, ← hc b]
    have hf1 : γ b 1 = r (M b) := by
      simp only [γ, AffineMap.lineMap_apply_one, polygonLinearParameter_natVertex, ← hc (M b)]
    obtain ⟨t, ht, hx⟩ := hr.crosscut_intersects_continuous_of_cyclic_order hs hdim
      a (M a) b (M b) hq0 hq1 (hS.symm ▸ hopen a) (γ b)
      (hΓ.comp AffineMap.lineMap_continuous).continuousOn hf0 hf1
      ((hcurve b).trans (hopen b))
      (by rw [hdist b hab.le]; omega)
      (by rw [hdist b hab.le, hdist (M a) (hab.trans hbMa).le]; omega)
      (by rw [hdist (M a) (hab.trans hbMa).le,
        hdist (M b) ((hab.trans hbMa).trans hMaMb).le]; omega)
    have hxA : γ b t ∈ T a := hB ▸ hx.1
    have hxB : γ b t ∈ T b := by
      obtain ⟨u, hu, heq⟩ := hcurve b ⟨t, ht, rfl⟩
      exact ⟨u, ⟨hu.1.le, hu.2.le⟩, heq⟩
    exact Set.disjoint_left.mp (hdis a b (ne_of_gt hab) (ne_of_lt hbMa)) hxA hxB
  refine ⟨M, hnon, heven, hfour, fun i => ⟨hopen i, hincidence i⟩, hq, hdis, ?_, ?_⟩
  · intro i
    simp only [hM i, min_comm, max_comm, and_self]
  · intro i t
    simp only [hM i, AffineMap.lineMap_apply_one_sub]

end PoincareConjecture.M25.Topology3D
