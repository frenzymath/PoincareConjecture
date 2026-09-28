import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finitePL_annulus_track_of_period {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L)
    (F g : (ℝ × (ℝ × ℝ)) → E)
    (hF : FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ rectangle (4 * L) d))
    (hperiod : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc 0 (4 * L),
      ∀ u : Icc (-d) d,
        g (t, annulusMap L (by linarith) ((s : AddCircle (4 * L)), u)) = F (t, (s, u))) :
    FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ squareAnnulus L d) := by
  classical
  have hL : 0 < L := by linarith
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨KI, hKI, hKIs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc zero_lt_one
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) (Icc (0 : ℝ) 1) := by
    rw [← hKIs]
    exact (KI.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)).finitePiecewiseAffineOn hKI
  have hpieces (i : Fin 4) :
      FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ stripRegion L d i) := by
    obtain ⟨c, hc, hcv⟩ := exists_rotated_strip_charts hd hwidth i
    obtain ⟨r, hr, hrv⟩ := hc.symm
    let A : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ) :=
      ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) ((i.val : ℝ) * L, 0)
    have hAr : FinitePiecewiseAffineOn (A ∘ r) (stripRegion L d i) :=
      hr.postcomp A.toContinuousAffineMap
    have hmap : MapsTo (A ∘ r) (stripRegion L d i) (rectangle (4 * L) d) := by
      intro x hx
      have hp : r x ∈ rectangle L d := by
        rw [← hrv ⟨x, hx⟩]
        exact (c.symm ⟨x, hx⟩).property
      change ((i.val : ℝ) * L + (r x).1 ∈ Icc 0 (4 * L)) ∧
        0 + (r x).2 ∈ Icc (-d) d
      refine ⟨?_, by simpa only [zero_add] using hp.2⟩
      fin_cases i <;> norm_num <;> constructor <;> linarith [hp.1.1, hp.1.2]
    have hcomp := hF.comp (hid.prodMap hAr) (by
      intro p hp
      exact ⟨hp.1, hmap hp.2⟩)
    apply hcomp.congr
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    let p : rectangle L d := c.symm ⟨x, hx⟩
    have hrp : r x = p := (hrv ⟨x, hx⟩).symm
    have hcp : (c p : ℝ × ℝ) = x := congrArg Subtype.val (c.apply_symm_apply _)
    have hsmall : 4 * |(p : ℝ × ℝ).2| < L :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr p.property.2) (by norm_num)) hwidth
    have hs : (p : ℝ × ℝ).1 + (i.val : ℝ) * L ∈ Icc 0 (4 * L) := by
      have h := (hmap hx).1
      change (i.val : ℝ) * L + (r x).1 ∈ Icc 0 (4 * L) at h
      simpa only [hrp, add_comm] using h
    have hpoint : annulusMap L hL
        ((((p : ℝ × ℝ).1 + (i.val : ℝ) * L : ℝ) : AddCircle (4 * L)),
          (p : ℝ × ℝ).2) = x := by
      rw [annulusMap_coe hL hsmall hs, wrappedStripMap_block hsmall p.property.1 i,
        ← hcv p, hcp]
    have hval := hperiod t ht _ hs ⟨(p : ℝ × ℝ).2, p.property.2⟩
    rw [hpoint] at hval
    change F (t, ((i.val : ℝ) * L + (r x).1, 0 + (r x).2)) = g (t, x)
    simpa only [hrp, zero_add, add_comm] using hval.symm
  have hall := FinitePiecewiseAffineOn.iUnion hpieces
  have hcover : (⋃ i : Fin 4, Icc (0 : ℝ) 1 ×ˢ stripRegion L d i) =
      Icc (0 : ℝ) 1 ×ˢ squareAnnulus L d := by
    rw [← union_four_strips hd.le (show 2 * d < L by linarith)]
    ext x
    simp only [mem_iUnion, mem_prod, mem_union]
    simp [Fin.exists_fin_succ, stripRegion]
    tauto
  rwa [hcover] at hall

end PoincareConjecture.M76.Dehn
