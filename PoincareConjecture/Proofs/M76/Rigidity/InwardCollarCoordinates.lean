import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs

set_option autoImplicit false

open Set Metric Geometry

namespace Geometry

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {c : E × ℝ → X}

theorem PolyhedralPLInCharts.finite_product_slice
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    PolyhedralPLInCharts e (fun z => c (z, t)) L.space := by
  let A : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E t)
  have hA : FinitePiecewiseAffineOn A L.space :=
    ⟨L, hL, rfl, L.affineOnFaces_affine A⟩
  exact hc.comp_finitePiecewiseAffineOn L hL hA (fun _ hz => ⟨hz, ht⟩)

end Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Q3" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X}

theorem ChartwisePLSphere.exists_finitePL_collar_base_parameter
    (s : ChartwisePLSphere e (frontier R))
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (HB : L.space ≃ₜ frontier R) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    (hbase : ∀ x : L.space, c ((x : E), 0) = HB x) :
    ∃ q : V3 → E, FinitePiecewiseAffineOn q Q3 ∧
      ∀ x : Q3, q x = (HB.symm (s.parametrization x) : E) := by
  classical
  let q : V3 → E := fun x => if hx : x ∈ Q3 then HB.symm (s.parametrization ⟨x, hx⟩) else 0
  have hqval (x : Q3) : q x = (HB.symm (s.parametrization x) : E) := by
    simp only [q, dif_pos x.property]
  have hqcont : ContinuousOn q Q3 := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (HB.symm.continuous.comp s.parametrization.continuous)
    convert h using 1
    funext x
    exact hqval x
  have hqmap : MapsTo q Q3 L.space := by
    intro x hx
    rw [hqval ⟨x, hx⟩]
    exact (HB.symm (s.parametrization ⟨x, hx⟩)).property
  have hbasePL : PolyhedralPLInCharts e (fun z => c (z, 0)) L.space :=
    PolyhedralPLInCharts.finite_product_slice L hL hc (by norm_num)
  have hbaseInj : InjOn (fun z => c (z, 0)) L.space := by
    intro x hx y hy hxy
    have hpairs := congrArg Subtype.val (hi.injective
      (a₁ := ⟨(x, 0), ⟨hx, by norm_num⟩⟩)
      (a₂ := ⟨(y, 0), ⟨hy, by norm_num⟩⟩) hxy)
    have hfirst := congrArg Prod.fst hpairs
    exact hfirst
  have hcomposite : PolyhedralPLInCharts e ((fun z => c (z, 0)) ∘ q) Q3 :=
    s.piecewiseAffine.congr (by
      intro x hx
      change s.map x = c (q x, 0)
      rw [hqval ⟨x, hx⟩, hbase, HB.apply_symm_apply]
      exact s.map_eq ⟨x, hx⟩)
  obtain ⟨K, hK, hKQ⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have h := hbasePL.finitePiecewiseAffineOn_lift hcompat hbaseInj K hK
    (hqcont.mono hKQ.subset) (fun _ hx => hqmap (hKQ.subset hx))
    (hKQ.symm ▸ hcomposite)
  exact ⟨q, hKQ ▸ h, hqval⟩

end PoincareConjecture.M76
