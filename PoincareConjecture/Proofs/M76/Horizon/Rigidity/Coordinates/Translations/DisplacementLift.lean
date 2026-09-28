import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.Translations.Vector
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardLiftPL
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V0" => (Fin 0 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0



theorem StandardLatticeHandleAtlas.finitePiecewiseAffineOn_displacement
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {Y Z : E → X0} (hY : PolyhedralPLInCharts d Y K.space)
    (hZ : PolyhedralPLInCharts d Z K.space)
    (w : E → V3) (hw : ContinuousOn w K.space)
    (htranslation : ∀ x ∈ K.space,
      hamiltonZeroTargetVectorTranslation (w x, Y x) = Z x) :
    FinitePiecewiseAffineOn w K.space := by
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  obtain ⟨i, J, O, hJ, hJK, hO, hxO, hOJ, hYi, hcoords⟩ := hY.coordinates x
  obtain ⟨a, ha⟩ := hd.inverse_formula i
  let v : E → V0 × V3 := a ∘ (d i) ∘ Y
  have hv : FinitePiecewiseAffineOn v J.space :=
    hcoords.postcomp a.toContinuousAffineMap
  have hproj (y : E) (hy : y ∈ J.space) :
      ((v y).1, QuotientAddGroup.mk (v y).2) = Y y := by
    change ((a (d i (Y y))).1, QuotientAddGroup.mk (a (d i (Y y))).2) = Y y
    rw [← ha _ ((d i).map_source (hYi hy)), (d i).left_inv (hYi hy)]
  let v' : E → V0 × V3 := fun y => ((v y).1, (v y).2 + w y)
  have hv' : FinitePiecewiseAffineOn v' J.space := by
    apply hd.finitePiecewiseAffineOn_lift J hJ Z (hZ.restrict_finite J hJ hJK) v'
      (hv.continuousOn.fst.prodMk (hv.continuousOn.snd.add (hw.mono hJK)))
    intro y hy
    change ((v y).1, QuotientAddGroup.mk ((v y).2 + w y)) = Z y
    rw [← hamiltonZeroTargetVectorTranslation_mk, hproj y hy]
    exact htranslation y (hJK hy)
  have hlocal : FinitePiecewiseAffineOn w J.space := by
    let hs := (ContinuousLinearMap.snd ℝ V0 V3).toContinuousAffineMap
    apply ((hv'.postcomp hs).sub (hv.postcomp hs)).congr
    intro y hy
    change (v y).2 + w y - (v y).2 = w y
    abel
  obtain ⟨P, hP, hPJ, hPL⟩ := hlocal
  refine ⟨P, O, hP, hO, hxO, ?_, hPL⟩
  rw [hPJ]
  exact hOJ

end PoincareConjecture.M76
