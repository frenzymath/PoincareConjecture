import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_ContactTime
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order













noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture



theorem m64Intrinsic_first_annulus_contact_unique
    {q : ℝ → AnnulusCoordinates} {R b d : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hbR : b ≤ R) (hdR : d ≤ R)
    (hbeforeb : ∀ t ∈ Ioo (0 : ℝ) b, 1 < ‖q t‖ ∧ ‖q t‖ < 2)
    (hbefored : ∀ t ∈ Ioo (0 : ℝ) d, 1 < ‖q t‖ ∧ ‖q t‖ < 2)
    (hcontactb : b = R ∨ ‖q b‖ = 1 ∨ ‖q b‖ = 2)
    (hcontactd : d = R ∨ ‖q d‖ = 1 ∨ ‖q d‖ = 2) : b = d := by
  rcases lt_trichotomy b d with hlt | heq | hlt
  · have h := hbefored b ⟨hb, hlt⟩
    rcases hcontactb with hR | h1 | h2
    · linarith
    · linarith [h.1]
    · linarith [h.2]
  · exact heq
  · have h := hbeforeb d ⟨hd, hlt⟩
    rcases hcontactd with hR | h1 | h2
    · linarith
    · linarith [h.1]
    · linarith [h.2]




theorem m64Intrinsic_isClosed_contact_window
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : Continuous u) (a b : ℝ) :
    IsClosed {s : ℝ | ∃ t ∈ Icc a b, ‖u (s, t)‖ ≤ 1 ∨ 2 ≤ ‖u (s, t)‖} := by
  let T := Icc a b
  let : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
  have hmap : Continuous (fun p : ℝ × T => u (p.1, p.2.val)) :=
    hu.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hC : IsClosed {p : ℝ × T | ‖u (p.1, p.2.val)‖ ≤ 1 ∨ 2 ≤ ‖u (p.1, p.2.val)‖} :=
    (isClosed_le hmap.norm continuous_const).union (isClosed_le continuous_const hmap.norm)
  have hprojection := isClosedMap_fst_of_compactSpace _ hC
  convert hprojection using 1
  ext s
  constructor
  · rintro ⟨t, ht, hbad⟩
    exact ⟨(s, ⟨t, ht⟩), hbad, rfl⟩
  · rintro ⟨⟨s, t⟩, hbad, rfl⟩
    exact ⟨t.val, t.property, hbad⟩




theorem m64Intrinsic_first_annulus_contact_measurable
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : Continuous u)
    {height : ℝ → ℝ} {R : ℝ}
    (hheight : ∀ s : ℝ, 0 < height s ∧ height s ≤ R ∧
      (∀ t ∈ Ioo (0 : ℝ) (height s), 1 < ‖u (s, t)‖ ∧ ‖u (s, t)‖ < 2) ∧
      (height s = R ∨ ‖u (s, height s)‖ = 1 ∨ ‖u (s, height s)‖ = 2)) :
    Measurable height := by
  apply measurable_of_Iic
  intro r
  by_cases hRr : R ≤ r
  · have heq : height ⁻¹' Iic r = univ := by
      ext s
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (hheight s).2.1.trans hRr
    rw [heq]
    exact MeasurableSet.univ
  · have hrR : r < R := lt_of_not_ge hRr
    have heq : height ⁻¹' Iic r = ⋃ n : ℕ,
        {s : ℝ | ∃ t ∈ Icc (1 / (n + 1 : ℝ)) r, ‖u (s, t)‖ ≤ 1 ∨ 2 ≤ ‖u (s, t)‖} := by
      ext s
      constructor
      · intro hs
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hheight s).1
        refine mem_iUnion.mpr ⟨n, height s, ⟨hn.le, hs⟩, ?_⟩
        rcases (hheight s).2.2.2 with heq | h1 | h2
        · exact False.elim ((not_lt_of_ge hs) (heq ▸ hrR))
        · exact Or.inl h1.le
        · exact Or.inr h2.ge
      · intro hs
        obtain ⟨n, t, ht, hbad⟩ := mem_iUnion.mp hs
        by_contra hn
        have hrt : r < height s := lt_of_not_ge hn
        have hpos : 0 < t := lt_of_lt_of_le (by positivity : 0 < 1 / (n + 1 : ℝ)) ht.1
        have hinside := (hheight s).2.2.1 t ⟨hpos, ht.2.trans_lt hrt⟩
        rcases hbad with hbad | hbad
        · exact not_lt_of_ge hbad hinside.1
        · exact not_lt_of_ge hbad hinside.2
    rw [heq]
    exact MeasurableSet.iUnion (fun n => (m64Intrinsic_isClosed_contact_window hu
      (1 / (n + 1 : ℝ)) r).measurableSet)




theorem m64Intrinsic_exists_measurable_contact_times
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : Continuous u) {R : ℝ} (hR : 0 < R)
    (henter : ∀ s : ℝ, ∃ eta : ℝ, 0 < eta ∧
      ∀ t ∈ Ioo (0 : ℝ) eta, 1 < ‖u (s, t)‖ ∧ ‖u (s, t)‖ < 2) :
    ∃ height : ℝ → ℝ, Measurable height ∧ ∀ s : ℝ,
      0 < height s ∧ height s ≤ R ∧
      (∀ t ∈ Ioo (0 : ℝ) (height s), 1 < ‖u (s, t)‖ ∧ ‖u (s, t)‖ < 2) ∧
      u (s, height s) ∈ standardAnnulusDomain ∧
      (height s = R ∨ ‖u (s, height s)‖ = 1 ∨ ‖u (s, height s)‖ = 2) := by
  have hexists (s : ℝ) : ∃ b : ℝ, 0 < b ∧ b ≤ R ∧
      (∀ t ∈ Ioo (0 : ℝ) b, 1 < ‖u (s, t)‖ ∧ ‖u (s, t)‖ < 2) ∧
      u (s, b) ∈ standardAnnulusDomain ∧
      (b = R ∨ ‖u (s, b)‖ = 1 ∨ ‖u (s, b)‖ = 2) := by
    obtain ⟨eta, heta, hinside⟩ := henter s
    exact m64Intrinsic_exists_first_annulus_contact
      (hu.comp (continuous_const.prodMk continuous_id)) hR heta hinside
  choose height hheight using hexists
  refine ⟨height, m64Intrinsic_first_annulus_contact_measurable hu (R := R) ?_, hheight⟩
  intro s
  exact ⟨(hheight s).1, (hheight s).2.1, (hheight s).2.2.1, (hheight s).2.2.2.2⟩

end PoincareConjecture
