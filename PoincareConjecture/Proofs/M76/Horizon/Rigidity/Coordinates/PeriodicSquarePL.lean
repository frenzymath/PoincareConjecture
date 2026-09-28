import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.PeriodicSquare
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall









set_option autoImplicit false
open Set Geometry

namespace Geometry

variable {E F V X ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X]

theorem PolyhedralPLInCharts.exists_image_of_finitePL_embedding
    {e : ι → OpenPartialHomeomorph X V} {u : E → F} {f : F → X} {S : Set E}
    (hu : FinitePiecewiseAffineOn u S) (hinj : InjOn u S)
    (hf : PolyhedralPLInCharts e (f ∘ u) S) :
    ∃ K : SimplicialComplex ℝ F,
      K.faces.Finite ∧ K.space = u '' S ∧ PolyhedralPLInCharts e f K.space := by
  obtain ⟨b, hb, hbval⟩ := hu.exists_homeomorph_image hinj
  obtain ⟨r, hr, hrval⟩ := hb.symm
  have hr' := hr
  obtain ⟨K, hK, hKs, _⟩ := hr'
  have hrmem (y : F) (hy : y ∈ K.space) : r y ∈ S := by
    have he := hrval ⟨y, hKs.subset hy⟩
    rw [← he]
    exact (b.symm ⟨y, hKs.subset hy⟩).property
  have hright (y : F) (hy : y ∈ K.space) : u (r y) = y := by
    have he := hrval ⟨y, hKs.subset hy⟩
    rw [← he, ← hbval, b.apply_symm_apply]
  refine ⟨K, hK, hKs, ?_⟩
  have hcomp := hf.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hr) hrmem
  exact hcomp.congr (fun y hy => congrArg f (hright y hy))

end Geometry

namespace PoincareConjecture.M76.PeriodicSquare

variable (p : ℝ) [Fact (0 < p)]

def halfInterval (b : Bool) : Set ℝ :=
  if b then Icc (p / 2) p else Icc 0 (p / 2)

def quarter (b : Bool × Bool) : Set (ℝ × ℝ) :=
  halfInterval p b.1 ×ˢ halfInterval p b.2

theorem halfInterval_subset (b : Bool) : halfInterval p b ⊆ Icc 0 p := by
  have hp := (Fact.out : 0 < p)
  cases b <;> simp only [halfInterval, Bool.false_eq_true, if_false, if_true]
  · intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  · intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩

theorem quarter_subset (b : Bool × Bool) : quarter p b ⊆ Icc 0 p ×ˢ Icc 0 p :=
  fun _ hx => ⟨halfInterval_subset p b.1 hx.1, halfInterval_subset p b.2 hx.2⟩

theorem iUnion_quarter : (⋃ b, quarter p b) = Icc 0 p ×ˢ Icc 0 p := by
  apply Subset.antisymm
  · exact iUnion_subset (quarter_subset p)
  · intro z hz
    have hex (x : ℝ) (hx : x ∈ Icc 0 p) : ∃ b, x ∈ halfInterval p b := by
      by_cases h : x ≤ p / 2
      · exact ⟨false, hx.1, h⟩
      · exact ⟨true, (le_of_not_ge h), hx.2⟩
    obtain ⟨b, hb⟩ := hex z.1 hz.1
    obtain ⟨c, hc⟩ := hex z.2 hz.2
    exact mem_iUnion.mpr ⟨(b, c), hb, hc⟩

theorem exists_finite_quarter (b : Bool × Bool) :
    ∃ K : SimplicialComplex ℝ (ℝ × ℝ), K.faces.Finite ∧ K.space = quarter p b := by
  have hp := (Fact.out : 0 < p)
  have hI (c : Bool) : IsFinitePLBallPair ℝ (halfInterval p c)
      (if c then {p / 2, p} else {0, p / 2}) := by
    cases c
    · exact isFinitePLBallPair_Icc (by linarith : (0 : ℝ) < p / 2)
    · exact isFinitePLBallPair_Icc (by linarith : p / 2 < p)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := (hI b.1).prod (hI b.2)
  exact ⟨K, hK, hKs⟩

theorem injOn_periodic_quarter (b : Bool × Bool) :
    InjOn (fun z : ℝ × ℝ => ((z.1 : AddCircle p), (z.2 : AddCircle p)))
      (quarter p b) := by
  have hp := (Fact.out : 0 < p)
  have hcoord (c : Bool) {x y : ℝ} (hx : x ∈ halfInterval p c)
      (hy : y ∈ halfInterval p c) (h : (x : AddCircle p) = (y : AddCircle p)) : x = y := by
    rcases (AddCircle.coe_eq_coe_iff_eq_or_endpoints
      (halfInterval_subset p c hx) (halfInterval_subset p c hy)).mp h with
      he | ⟨hx0, hyp⟩ | ⟨hxp, hy0⟩
    · exact he
    · cases c <;> simp only [halfInterval, Bool.false_eq_true, if_false, if_true] at hx hy
      · linarith [hy.2]
      · linarith [hx.1]
    · cases c <;> simp only [halfInterval, Bool.false_eq_true, if_false, if_true] at hx hy
      · linarith [hx.2]
      · linarith [hy.1]
  intro z hz w hw he
  exact Prod.ext (hcoord b.1 hz.1 hw.1 (congrArg Prod.fst he))
    (hcoord b.2 hz.2 hw.2 (congrArg Prod.snd he))

theorem polyhedralPL_descent
    {E V X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V)
    (he : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hc : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (u : ℝ × ℝ → E) (hu : FinitePiecewiseAffineOn u (Icc 0 p ×ˢ Icc 0 p))
    (himage : u '' (Icc 0 p ×ˢ Icc 0 p) = J.space)
    (hfib : ∀ z w : Square p,
      u (z.1, z.2) = u (w.1, w.2) → projection p z = projection p w)
    (f : E → X) (hf : ContinuousOn f J.space)
    (hcomp : PolyhedralPLInCharts e (f ∘ u) (Icc 0 p ×ˢ Icc 0 p)) :
    PolyhedralPLInCharts e f J.space := by
  have hpieces (b : Bool × Bool) : ∃ K : SimplicialComplex ℝ E,
      K.faces.Finite ∧ K.space = u '' quarter p b ∧ PolyhedralPLInCharts e f K.space := by
    obtain ⟨L, hL, hLs⟩ := exists_finite_quarter p b
    have hsub : L.space ⊆ Icc 0 p ×ˢ Icc 0 p := hLs.subset.trans (quarter_subset p b)
    have hi : InjOn u L.space := by
      intro z hz w hw heq
      exact injOn_periodic_quarter p b (hLs.subset hz) (hLs.subset hw)
        (hfib (⟨z.1, (hsub hz).1⟩, ⟨z.2, (hsub hz).2⟩)
          (⟨w.1, (hsub hw).1⟩, ⟨w.2, (hsub hw).2⟩) heq)
    simpa only [hLs] using (hcomp.restrict_finite L hL hsub).exists_image_of_finitePL_embedding
      (hu.restrict L hL hsub) hi
  choose K hK hKs hPL using hpieces
  apply polyhedralPLInCharts_of_finite_cover he hc J hJ K hK hf hPL
  intro x hx
  obtain ⟨z, hz, rfl⟩ := himage.symm.subset hx
  obtain ⟨b, hb⟩ := mem_iUnion.mp ((iUnion_quarter p).symm.subset hz)
  exact mem_iUnion.mpr ⟨b, (hKs b).symm.subset ⟨z, hb, rfl⟩⟩

end PoincareConjecture.M76.PeriodicSquare
