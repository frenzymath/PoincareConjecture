import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcCellPreparation
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcFiniteJunctions
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcCellStraightening
import PoincareConjecture.Proofs.M25.Topology3D.Plane.InscribedIntervals









set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 800000 in


theorem exists_relative_polygonalArc_straightening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) (n : ℕ)
    (A B : E) (X : E →ₗ[ℝ] ℝ) (hAB : X A < X B)
    (q : ℝ → Polygon E (n + 2))
    (hq_smooth : ∀ j, ContDiff ℝ ∞ (fun t => q t j))
    (hq_good : ∀ t, IsSimplePolygonalArc (q t) ∧ q t 0 = A ∧
      q t (Fin.last (n + 1)) = B ∧ ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) →
        X A < X (q t j) ∧ X (q t j) < X B)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4)
    (hflat0 : ∀ t, |t| < ε → ∀ j, q t j ∈ segment ℝ A B)
    (hflat1 : ∀ t, |t - 1| < ε → ∀ j, q t j ∈ segment ℝ A B) :
    ∃ ν : ℝ, 0 < ν ∧ ν < ε ∧ ∃ Q : ℝ × ℝ → Polygon E (n + 2),
      (∀ j, ContDiff ℝ ∞ (fun z => Q z j)) ∧
      (∀ s t, IsSimplePolygonalArc (Q (s, t)) ∧ Q (s, t) 0 = A ∧
        Q (s, t) (Fin.last (n + 1)) = B ∧
        ∀ j, j ≠ 0 → j ≠ Fin.last (n + 1) →
          X A < X (Q (s, t) j) ∧ X (Q (s, t) j) < X B) ∧
      (∀ s t, s ≤ 0 → Q (s, t) = q t) ∧
      (∀ s t, 1 ≤ s → Q (s, t) = Q (1, t)) ∧
      (∀ s t, t ≤ ν ∨ 1 - ν ≤ t → Q (s, t) = q t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, Q (1, t) j ∈ segment ℝ A B := by
  classical
  induction n generalizing ε with
  | zero =>
      refine ⟨ε / 2, half_pos hε, half_lt_self hε, (fun z => q z.2),
        (fun j => (hq_smooth j).comp contDiff_snd), (fun _ t => hq_good t),
        (fun _ _ _ => rfl), (fun _ _ _ => rfl), (fun _ _ _ => rfl), ?_⟩
      intro t _ j
      fin_cases j
      · change q t 0 ∈ segment ℝ A B
        rw [(hq_good t).2.1]
        exact left_mem_segment ℝ A B
      · change q t (Fin.last 1) ∈ segment ℝ A B
        rw [(hq_good t).2.2.1]
        exact right_mem_segment ℝ A B
  | succ n ih =>
      have hflat : ∀ t, t ∈ Ioo (-ε) ε ∪ Ioo (1 - ε) (1 + ε) →
          ∀ j, q t j ∈ segment ℝ A B := by
        intro t ht j
        rcases ht with ht | ht
        · exact hflat0 t (abs_lt.mpr ht) j
        · exact hflat1 t (by
            apply abs_lt.mpr
            constructor <;> linarith [ht.1, ht.2]) j
      obtain ⟨N, hN, c, ρ, ν₀, hρ, hρ', hν₀, hν₀ε, hcompat, P,
        hPs, hPg, hP0, hP1, hPtail, hPflat, hPstraight⟩ :=
        exists_relative_polygonalArc_cell_preparation hdim A B X hAB q
          hq_smooth hq_good hε hε' hflat
      let H : ℝ → Polygon E (n + 3) := fun t => P (1, t)
      have hHs (j : Fin (n + 3)) : ContDiff ℝ ∞ (fun t => H t j) :=
        (hPs j).comp (contDiff_const.prodMk contDiff_id)
      have hHg (t : ℝ) := hPg 1 t
      have hHflat (t : ℝ) (ht : t ∈ Ioo (-ε) ε ∪ Ioo (1 - ε) (1 + ε)) :
          ∀ j, H t j ∈ segment ℝ A B := hPflat 1 t ht
      have hHstraight (i : Fin N) (t : ℝ)
          (ht : t ∈ Ioo ((i.val : ℝ) / N - ρ) (((i.val : ℝ) + 1) / N + ρ)) :
          H t (c i).castSucc.succ ∈ segment ℝ
            (H t ((finRotate (n + 3)).symm (c i).castSucc.succ))
            (H t (finRotate (n + 3) (c i).castSucc.succ)) := hPstraight i t ht
      obtain ⟨η, hη, hηρ, J, hJs, hJg, hJ0, hJ1, hJtail, hJstraight, hJflat⟩ :=
        exists_relative_polygonalArc_finite_junctions hdim A B X hAB hε hε'
          hN c hρ hρ' hcompat H hHs hHg hHflat hHstraight
      let V : ℝ → Polygon E (n + 3) := fun t => J (1, t)
      have hVs (j : Fin (n + 3)) : ContDiff ℝ ∞ (fun t => V t j) :=
        (hJs j).comp (contDiff_const.prodMk contDiff_id)
      have hVg (t : ℝ) := hJg 1 t
      have hVflat (k : Fin (N + 1)) (t : ℝ) (ht : |t - (k.val : ℝ) / N| < η) :
          ∀ j, V t j ∈ segment ℝ A B := hJflat k t ht
      have hVstraight (i : Fin N) (s t : ℝ)
          (ht : t ∈ Ioo ((i.val : ℝ) / N - ρ) (((i.val : ℝ) + 1) / N + ρ)) :
          J (s, t) (c i).castSucc.succ ∈ segment ℝ
            (J (s, t) ((finRotate (n + 3)).symm (c i).castSucc.succ))
            (J (s, t) (finRotate (n + 3) (c i).castSucc.succ)) :=
        hJstraight s t i ht
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      let a (i : Fin N) : ℝ := (i.val : ℝ) / N
      let b (i : Fin N) : ℝ := ((i.val + 1 : ℕ) : ℝ) / N
      have ha0 (i : Fin N) : 0 ≤ a i := by
        dsimp [a]
        positivity
      have hb1 (i : Fin N) : b i ≤ 1 := by
        dsimp [b]
        apply (div_le_one hNR).mpr
        exact_mod_cast i.isLt
      have hab (i : Fin N) : a i < b i := by
        dsimp [a, b]
        apply (div_lt_div_iff_of_pos_right hNR).mpr
        norm_num
      have hfa (i : Fin N) (t : ℝ) (ht : |t - a i| < η) :
          ∀ j, V t j ∈ segment ℝ A B := by
        have hk := hVflat i.castSucc t (by simpa [a] using ht)
        simpa [V, a] using hk
      have hfb (i : Fin N) (t : ℝ) (ht : |t - b i| < η) :
          ∀ j, V t j ∈ segment ℝ A B := by
        have hk := hVflat i.succ t (by simpa [b] using ht)
        simpa [V, b] using hk
      have hcell (i : Fin N) : ∃ σ : ℝ, 0 < σ ∧ σ < (b i - a i) / 4 ∧
          ∃ R : ℝ × ℝ → Polygon E (n + 3),
            (∀ j, ContDiff ℝ ∞ (fun z => R z j)) ∧
            (∀ s t, IsSimplePolygonalArc (R (s, t)) ∧ R (s, t) 0 = A ∧
              R (s, t) (Fin.last (n + 2)) = B ∧
              ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
                X A < X (R (s, t) j) ∧ X (R (s, t) j) < X B) ∧
            (∀ s t, s ≤ 0 → R (s, t) = V t) ∧
            (∀ s t, 1 ≤ s → R (s, t) = R (1, t)) ∧
            (∀ s t, t ≤ a i + σ ∨ b i - σ ≤ t → R (s, t) = V t) ∧
            ∀ t ∈ Icc (a i) (b i), ∀ j, R (1, t) j ∈ segment ℝ A B := by
        apply exists_relative_polygonalArc_cell_straightening A B X hAB ih V
          (c i) hVs hVg (hab i) hρ hη
        · intro t ht
          exact hVstraight i 1 t (by simpa [a, b] using ht)
        · exact hfa i
        · exact hfb i
      choose σ hσ hσh R hRs hRg hR0 hR1 hRtail hRflat using hcell
      let S : Finset ℝ := insert ν₀ (insert (ε / 8) (Finset.univ.image σ))
      have hS : S.Nonempty := ⟨ν₀, Finset.mem_insert_self _ _⟩
      have hSpos (x : ℝ) (hx : x ∈ S) : 0 < x := by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hν₀
        · rcases Finset.mem_insert.mp hx with rfl | hx
          · positivity
          · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
            exact hσ i
      let ν : ℝ := S.min' hS / 2
      have hνpos : 0 < ν := by
        dsimp [ν]
        exact half_pos (hSpos _ (Finset.min'_mem _ _))
      have hνν₀ : ν < ν₀ := by
        dsimp [ν]
        exact (half_lt_self (hSpos _ (Finset.min'_mem _ _))).trans_le
          (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
      have hνε8 : ν < ε / 8 := by
        dsimp [ν]
        exact (half_lt_self (hSpos _ (Finset.min'_mem _ _))).trans_le
          (Finset.min'_le _ _ (Finset.mem_insert_of_mem
            (Finset.mem_insert_self (ε / 8) (Finset.univ.image σ))))
      have hνσ (i : Fin N) : ν < σ i := by
        dsimp [ν]
        have hmem : σ i ∈ S := Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨i, Finset.mem_univ _, rfl⟩))
        exact (half_lt_self (hSpos _ (Finset.min'_mem _ _))).trans_le
          (Finset.min'_le _ _ hmem)
      have hνε : ν < ε := lt_of_lt_of_le hνε8 (by linarith)
      have hmesh (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
          ∃ i : Fin N, t ∈ Icc (a i) (b i) := by
        let τ : Fin (N + 1) → ℝ := fun k => (k.val : ℝ) / N
        have hτ0 : τ 0 = 0 := by simp [τ]
        have hτN : τ (Fin.last N) = 1 := by
          dsimp [τ]
          exact div_self (ne_of_gt hNR)
        obtain ⟨i, hi⟩ := exists_mem_adjacent_mesh_interval hN τ (x := t) (by
          simpa [hτ0, hτN] using ht)
        refine ⟨i, ?_⟩
        simpa [a, b, τ] using hi
      let C : ℝ × ℝ → Polygon E (n + 3) := fun z =>
        ⟨fun j => V z.2 j + ∑ i : Fin N, (R i z j - V z.2 j)⟩
      have hCcell (i : Fin N) (s t : ℝ) (ht : t ∈ Icc (a i) (b i)) :
          C (s, t) = R i (s, t) := by
        apply congrArg Polygon.mk
        funext j
        change V t j + ∑ k : Fin N, (R k (s, t) j - V t j) = R i (s, t) j
        rw [Finset.sum_eq_single i]
        · abel
        · intro k _ hki
          have hvals : i.val ≠ k.val := fun hv => hki (Fin.ext hv.symm)
          rcases lt_or_gt_of_ne hvals with hik | hki'
          · have hnum : i.val + 1 ≤ k.val := Nat.succ_le_of_lt hik
            have hnumR : ((i.val + 1 : ℕ) : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast hnum
            have hbk : b i ≤ a k := by
              dsimp [a, b]
              exact (div_le_div_iff_of_pos_right hNR).mpr hnumR
            rw [hRtail k s t (Or.inl (by linarith [ht.2, hbk, hσ k]))]
            simp
          · have hnum : k.val + 1 ≤ i.val := Nat.succ_le_of_lt hki'
            have hnumR : ((k.val + 1 : ℕ) : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hnum
            have hbk : b k ≤ a i := by
              dsimp [a, b]
              exact (div_le_div_iff_of_pos_right hNR).mpr hnumR
            rw [hRtail k s t (Or.inr (by linarith [ht.1, hbk, hσ k]))]
            simp
        · simp
      have hCoutside (s t : ℝ) (ht : t ≤ 0 ∨ 1 ≤ t) : C (s, t) = V t := by
        apply congrArg Polygon.mk
        funext j
        change V t j + ∑ k : Fin N, (R k (s, t) j - V t j) = V t j
        have hz : ∑ k : Fin N, (R k (s, t) j - V t j) = 0 :=
          Finset.sum_eq_zero (fun k _ => by
            rw [hRtail k s t]
            · simp
            · rcases ht with ht | ht
              · exact Or.inl (by linarith [ha0 k, hσ k])
              · exact Or.inr (by linarith [hb1 k, hσ k]))
        rw [hz, add_zero]
      have hCg (s t : ℝ) : IsSimplePolygonalArc (C (s, t)) ∧
          C (s, t) 0 = A ∧ C (s, t) (Fin.last (n + 2)) = B ∧
          ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
            X A < X (C (s, t) j) ∧ X (C (s, t) j) < X B := by
        by_cases ht : t ∈ Icc (0 : ℝ) 1
        · obtain ⟨i, hi⟩ := hmesh t ht
          rw [hCcell i s t hi]
          exact hRg i s t
        · by_cases ht0 : t < 0
          · rw [hCoutside s t (Or.inl (le_of_lt ht0))]
            exact hVg t
          · have ht1 : 1 < t := by
              exact lt_of_not_ge (fun h => ht ⟨by linarith, h⟩)
            rw [hCoutside s t (Or.inr (le_of_lt ht1))]
            exact hVg t
      have hCs (j : Fin (n + 3)) : ContDiff ℝ ∞ (fun z => C z j) := by
        exact ((hVs j).comp contDiff_snd).add (ContDiff.sum (fun i _ =>
          (hRs i j).sub ((hVs j).comp contDiff_snd)))
      have hC0 (s t : ℝ) (hs : s ≤ 0) : C (s, t) = V t := by
        apply congrArg Polygon.mk
        funext j
        change V t j + ∑ k : Fin N, (R k (s, t) j - V t j) = V t j
        have hz : ∑ k : Fin N, (R k (s, t) j - V t j) = 0 :=
          Finset.sum_eq_zero (fun k _ => by rw [hR0 k s t hs, sub_self])
        rw [hz, add_zero]
      have hC1 (s t : ℝ) (hs : 1 ≤ s) : C (s, t) = C (1, t) := by
        apply congrArg Polygon.mk
        funext j
        change V t j + ∑ k : Fin N, (R k (s, t) j - V t j) =
          V t j + ∑ k : Fin N, (R k (1, t) j - V t j)
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [hR1 k s t hs]
      have hCtail (s t : ℝ) (ht : t ≤ ν ∨ 1 - ν ≤ t) : C (s, t) = V t := by
        apply congrArg Polygon.mk
        funext j
        change V t j + ∑ k : Fin N, (R k (s, t) j - V t j) = V t j
        have hz : ∑ k : Fin N, (R k (s, t) j - V t j) = 0 :=
          Finset.sum_eq_zero (fun k _ => by
            rw [hRtail k s t]
            · simp
            · rcases ht with ht | ht
              · exact Or.inl (by linarith [ha0 k, hνσ k])
              · exact Or.inr (by linarith [hb1 k, hνσ k]))
        rw [hz, add_zero]
      have hCflat (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
          ∀ j, C (1, t) j ∈ segment ℝ A B := by
        obtain ⟨i, hi⟩ := hmesh t ht
        rw [hCcell i 1 t hi]
        exact hRflat i t hi
      let Q : ℝ × ℝ → Polygon E (n + 3) := fun z =>
        ⟨fun j => P (3 * z.1, z.2) j + J (3 * z.1 - 1, z.2) j +
          C (3 * z.1 - 2, z.2) j - H z.2 j - V z.2 j⟩
      have hPcomp (j : Fin (n + 3)) :
          ContDiff ℝ ∞ (fun z : ℝ × ℝ => P (3 * z.1, z.2) j) := by
        exact (hPs j).comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd)
      have hJcomp (j : Fin (n + 3)) :
          ContDiff ℝ ∞ (fun z : ℝ × ℝ => J (3 * z.1 - 1, z.2) j) := by
        exact (hJs j).comp
          (((contDiff_const.mul contDiff_fst).sub
            (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (1 : ℝ)))).prodMk
            contDiff_snd)
      have hCcomp (j : Fin (n + 3)) :
          ContDiff ℝ ∞ (fun z : ℝ × ℝ => C (3 * z.1 - 2, z.2) j) := by
        exact (hCs j).comp
          (((contDiff_const.mul contDiff_fst).sub
            (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (2 : ℝ)))).prodMk
            contDiff_snd)
      have hHcomp (j : Fin (n + 3)) :
          ContDiff ℝ ∞ (fun z : ℝ × ℝ => H z.2 j) :=
        (hHs j).comp contDiff_snd
      have hVcomp (j : Fin (n + 3)) :
          ContDiff ℝ ∞ (fun z : ℝ × ℝ => V z.2 j) :=
        (hVs j).comp contDiff_snd
      have hQs (j : Fin (n + 3)) : ContDiff ℝ ∞ (fun z => Q z j) := by
        exact (((hPcomp j).add (hJcomp j)).add (hCcomp j)).sub (hHcomp j) |>.sub
          (hVcomp j)
      have hQleft (s t : ℝ) (hs : s ≤ 1 / 3) :
          Q (s, t) = P (3 * s, t) := by
        apply congrArg Polygon.mk
        funext j
        change P (3 * s, t) j + J (3 * s - 1, t) j + C (3 * s - 2, t) j -
          H t j - V t j = P (3 * s, t) j
        rw [hJ0 _ _ (by linarith), hC0 _ _ (by linarith)]
        abel
      have hQmiddle (s t : ℝ) (hs0 : 1 / 3 ≤ s) (hs1 : s ≤ 2 / 3) :
          Q (s, t) = J (3 * s - 1, t) := by
        apply congrArg Polygon.mk
        funext j
        change P (3 * s, t) j + J (3 * s - 1, t) j + C (3 * s - 2, t) j -
          H t j - V t j = J (3 * s - 1, t) j
        rw [hP1 _ _ (by linarith), hC0 _ _ (by linarith)]
        abel
      have hQright (s t : ℝ) (hs : 2 / 3 ≤ s) :
          Q (s, t) = C (3 * s - 2, t) := by
        apply congrArg Polygon.mk
        funext j
        change P (3 * s, t) j + J (3 * s - 1, t) j + C (3 * s - 2, t) j -
          H t j - V t j = C (3 * s - 2, t) j
        rw [hP1 _ _ (by linarith), hJ1 _ _ (by linarith)]
        abel
      have hQg (s t : ℝ) : IsSimplePolygonalArc (Q (s, t)) ∧
          Q (s, t) 0 = A ∧ Q (s, t) (Fin.last (n + 2)) = B ∧
          ∀ j, j ≠ 0 → j ≠ Fin.last (n + 2) →
            X A < X (Q (s, t) j) ∧ X (Q (s, t) j) < X B := by
        by_cases hs : s ≤ 1 / 3
        · rw [hQleft s t hs]
          exact hPg (3 * s) t
        · by_cases hs' : s ≤ 2 / 3
          · rw [hQmiddle s t (le_of_not_ge hs) hs']
            exact hJg (3 * s - 1) t
          · rw [hQright s t (le_of_not_ge hs')]
            exact hCg (3 * s - 2) t
      have hQ0 (s t : ℝ) (hs : s ≤ 0) : Q (s, t) = q t := by
        apply congrArg Polygon.mk
        funext j
        change P (3 * s, t) j + J (3 * s - 1, t) j + C (3 * s - 2, t) j -
          H t j - V t j = q t j
        rw [hP0 _ _ (by linarith), hJ0 _ _ (by linarith), hC0 _ _ (by linarith)]
        abel
      have hQ1 (s t : ℝ) (hs : 1 ≤ s) : Q (s, t) = Q (1, t) := by
        rw [hQright s t (by linarith), hQright 1 t (by norm_num)]
        have hst : 1 ≤ 3 * s - 2 := by linarith
        rw [hC1 _ _ hst]
        norm_num
      have hQtail (s t : ℝ) (ht : t ≤ ν ∨ 1 - ν ≤ t) : Q (s, t) = q t := by
        apply congrArg Polygon.mk
        funext j
        change P (3 * s, t) j + J (3 * s - 1, t) j + C (3 * s - 2, t) j -
          H t j - V t j = q t j
        have hPtail' : P (3 * s, t) = q t := hPtail _ _ (by
          rcases ht with ht | ht
          · exact Or.inl (by linarith [hνν₀])
          · exact Or.inr (by linarith [hνν₀]))
        have hJtail' : J (3 * s - 1, t) = H t := hJtail _ _ (by
          rcases ht with ht | ht
          · exact Or.inl (by linarith [hνε8])
          · exact Or.inr (by linarith [hνε8]))
        have hVtail : V t = H t := by
          change J (1, t) = H t
          exact hJtail 1 t (by
            rcases ht with ht | ht
            · exact Or.inl (by linarith [hνε8])
            · exact Or.inr (by linarith [hνε8]))
        rw [hPtail', hJtail', hCtail _ _ ht, hVtail]
        abel
      have hQflat (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : Fin (n + 3)) :
          Q (1, t) j ∈ segment ℝ A B := by
        rw [hQright 1 t (by norm_num)]
        rw [show (3 : ℝ) * 1 - 2 = 1 by norm_num]
        exact hCflat t ht j
      refine ⟨ν, hνpos, hνε, Q, hQs, hQg, hQ0, hQ1, hQtail, hQflat⟩

end PoincareConjecture.M25.Topology3D
