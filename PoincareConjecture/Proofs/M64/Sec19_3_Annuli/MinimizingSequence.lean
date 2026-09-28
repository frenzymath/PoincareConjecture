import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MinimalAnnulusInterface

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {c0 c1 : ℝ → M}

theorem m64Annulus_exists_minimizing_sequence
    (A : M64Annulus g c0 c1) :
    ∃ seq : ℕ → M64Annulus g c0 c1,
      Antitone (fun k => (seq k).area) ∧
        Tendsto (fun k => (seq k).area) atTop
          (𝓝 (m64LeastAnnulusArea g c0 c1)) := by
  have hnonempty := m64AnnulusAreaRange_nonempty A
  have hbounded := m64AnnulusAreaRange_bddBelow g c0 c1
  obtain ⟨u, huanti, hlim, humem⟩ := exists_seq_tendsto_sInf hnonempty hbounded
  choose seq hseq using humem
  refine ⟨seq, ?_, ?_⟩
  · simpa only [hseq] using huanti
  · simpa only [hseq, m64LeastAnnulusArea] using hlim

structure M64AnnulusRegularityCertificate
    (A : M64Annulus g c0 c1) : Prop where
  piecewise_c1 : M64PiecewiseC1Annulus A
  interior_smooth : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map
    (interior m64AnnulusDomain)

def m64MinimalAnnulusData_of_certificates
    (A : M64Annulus g c0 c1)
    (hmin : A.area = m64LeastAnnulusArea g c0 c1)
    (regularity : M64AnnulusRegularityCertificate A) :
    M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1) :=
  { annulus := A
    area_minimal := hmin
    piecewise_c1 := regularity.piecewise_c1
    interior_smooth := regularity.interior_smooth }

def m64MinimalAnnulusData_of_isLeast
    (B : M64Annulus g c0 c1)
    (hB : ∀ C : M64Annulus g c0 c1, B.area ≤ C.area)
    (regularity : M64AnnulusRegularityCertificate B) :
    M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1) :=
  m64MinimalAnnulusData_of_certificates B
    (m64LeastAnnulusArea_eq_of_isLeast B hB) regularity

end PoincareConjecture
