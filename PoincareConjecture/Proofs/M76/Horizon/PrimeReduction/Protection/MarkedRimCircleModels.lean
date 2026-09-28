import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.CircleComplexPolygon
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.PolygonCircleModels

set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex

theorem exists_marked_finitePL_circle_models
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2)
    (S : ι → Set E) (H : ∀ i, S i ≃ₜ Circle)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : (⋃ i, S i) = K.space) :
    ∃ (J : ι → SimplicialComplex ℝ E)
      (gamma : ∀ i, Metric.sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (J i).space),
      (∀ i, J i ≤ K ∧ (J i).faces.Finite ∧ (J i).space = S i ∧
        (gamma i).IsFinitePL) ∧
      (∀ t, t ∈ K.faces ↔ ∃ i, t ∈ (J i).faces) := by
  classical
  have hS (i : ι) : IsClosed (S i) :=
    (isCompact_iff_compactSpace.mpr (H i).symm.compactSpace).isClosed
  obtain ⟨J,hJK,hJS,hfaces⟩ :=
    PoincareConjecture.M76.Dehn.Annuli.exists_subcomplexes_of_disjoint_closed_cover
      K hK S hS hdis hcover
  have hgamma (i : ι) :
      ∃ gamma : Metric.sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (J i).space, gamma.IsFinitePL := by
    obtain ⟨n,P,hi,hP,hPs⟩ := (J i).exists_polygon_of_homeomorph_circle
      (hK.subset (hJK i)) (fun s hs => hdim s (hJK i hs))
      ((Homeomorph.setCongr (hJS i)).trans (H i))
    obtain ⟨gamma,hg⟩ := P.exists_finitePL_square_circle hP hi
    exact ⟨gamma.trans (Homeomorph.setCongr hPs),hg.setCongr rfl hPs⟩
  choose gamma hg using hgamma
  exact ⟨J,gamma,fun i => ⟨hJK i,hK.subset (hJK i),hJS i,hg i⟩,hfaces⟩

end Geometry.SimplicialComplex
