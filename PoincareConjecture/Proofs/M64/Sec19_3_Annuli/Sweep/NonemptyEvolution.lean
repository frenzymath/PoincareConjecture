import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.AnnulusJoin
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.SweptAnnulus
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ElementaryFields












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}




theorem m64Annulus_nonempty_of_c2_sweeps
    (hcompact : IsCompact (univ : Set M))
    {c0 c1 : ℝ → ℝ → M}
    (hc0 : M63C2ShrinkingCurveOn F c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn F c1 (Icc a b))
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (A : M64Annulus (F.metric s) (fun x => c0 x s) (fun x => c1 x s)) :
    Nonempty (M64Annulus (F.metric t) (fun x => c0 x t) (fun x => c1 x t)) := by
  obtain ⟨B, _⟩ := m64Annulus_transport_time F hcompact hs ht A
  obtain ⟨S0, _⟩ := m64Annulus_of_c2_sweep hc0 (F.metric t) ht hs
  obtain ⟨S1, _⟩ := m64Annulus_of_c2_sweep hc1 (F.metric t) hs ht
  obtain ⟨C, _⟩ := m64Annulus_join S0 B
  obtain ⟨D, _⟩ := m64Annulus_join C S1
  exact ⟨D⟩



theorem m64AnnulusFlow_nonempty_of_initial
    (hcompact : IsCompact (univ : Set M))
    {circumference : ℝ} (hcirc : 0 < circumference)
    (P : M62.CircleProductData F circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    (A : M64Annulus (P.flow.metric a) (fun x => c0 x a) (fun x => c1 x a)) :
    ∀ t ∈ Icc a b, Nonempty (M64Annulus (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t)) := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Fact (0 < circumference) := ⟨hcirc⟩
  have hcompactP : IsCompact (univ : Set P.charts.Point) := isCompact_univ
  intro t ht
  exact m64Annulus_nonempty_of_c2_sweeps hcompactP hc0 hc1
    ⟨le_rfl, ht.1.trans ht.2⟩ ht A



theorem m64AnnulusFlow_nonnegative_of_initial
    (hcompact : IsCompact (univ : Set M))
    {circumference : ℝ} (hcirc : 0 < circumference)
    (P : M62.CircleProductData F circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    (A : M64Annulus (P.flow.metric a) (fun x => c0 x a) (fun x => c1 x a)) :
    ∀ t ∈ Icc a b, 0 ≤ m64FlowAnnulusArea P c0 c1 t :=
  (m64AnnulusFlow_elementary_fields
    (m64AnnulusFlow_nonempty_of_initial hcompact hcirc P hc0 hc1 A)).2.2

end PoincareConjecture
