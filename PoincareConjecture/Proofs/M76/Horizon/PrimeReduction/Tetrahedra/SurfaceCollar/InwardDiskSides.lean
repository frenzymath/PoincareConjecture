import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.InwardAnnulus
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.InwardShellSide

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "D" => closedBall (0 : P2) 1
local notation "rim" => sphere (0 : P2) 1

theorem ChartwisePLSphere.exists_inward_disk_with_closed_complement
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S R O : Set X}
    (s : ChartwisePLSphere e S) (d : Fin 2 → Set V3) {r : Set V3}
    (hd : ∀ i, IsFinitePLBallPair P2 (d i) r)
    (hwhole : d 0 ∪ d 1 = Sphere) (hinter : d 0 ∩ d 1 = r)
    (hR : IsClosed R) (hO : IsOpen O) (hrO : s.map '' r ⊆ O)
    (hrfront : s.map '' r ⊆ frontier R)
    (hisolate : (S ∩ O) ∩ frontier R ⊆ s.map '' r)
    (hinward : (s.map '' r ∩ closure (S ∩ interior R)).Nonempty) :
    ∃ (a : ℝ) (f : P2 → X) (E : Set X),
      0 < a ∧ a < 1 ∧ PolyhedralPLInCharts e f D ∧ InjOn f D ∧
      MapsTo f D S ∧ f '' rim = s.map '' r ∧ IsClosed E ∧
      (f '' D) ∪ E = S ∧ (f '' D) ∩ E = f '' rim ∧
      f '' {x : P2 | ‖x‖ ∈ Icc a 1} ⊆ O ∧
      f '' {x : P2 | ‖x‖ ∈ Icc a 1} ⊆ R ∧
      (f '' {x : P2 | ‖x‖ ∈ Icc a 1}) \ (f '' rim) ⊆ interior R ∧
      ((s.map '' r ∩ closure (S ∩ Rᶜ)).Nonempty →
        ∀ P : Set X, IsPreconnected P → P ⊆ S → P ⊆ R →
          (P ∩ s.map '' r).Nonempty → P ⊆ f '' D) := by
  obtain ⟨i,a,f,k,q,b,ha,ha1,_,hfi,hfd,hfr,_,_,hb,hkp,hkb,_,hkr,_,hbSO,_,hsf,hbin,_,_,_,_⟩ :=
    s.exists_inward_annulus_of_parameter_cut d hd hwhole hinter hO hrO hrfront hisolate hinward
  have hdS (j : Fin 2) : d j ⊆ Sphere := by
    fin_cases j
    · exact subset_union_left.trans hwhole.subset
    · exact subset_union_right.trans hwhole.subset
  have hfS : MapsTo f D Sphere := fun x hx => hdS i (hfd.subset ⟨x,hx,rfl⟩)
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hsimage : s.map '' Sphere = S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      rw [s.map_eq ⟨y,hy⟩]
      exact (s.parametrization ⟨y,hy⟩).property
    · intro hx
      refine ⟨s.parametrization.symm ⟨x,hx⟩,(s.parametrization.symm ⟨x,hx⟩).property,?_⟩
      rw [s.map_eq]
      exact congrArg Subtype.val (s.parametrization.apply_symm_apply ⟨x,hx⟩)
  let E := s.map '' d i.rev
  have hother : IsClosed E := ((hd i.rev).isCompact.image_of_continuousOn
    (s.piecewiseAffine.continuousOn.mono (hdS i.rev))).isClosed
  have hcompD : (s.map ∘ f) '' D = s.map '' d i := by rw [image_comp,hfd]
  have hcompr : (s.map ∘ f) '' rim = s.map '' r := by rw [image_comp,hfr]
  have hcompb : (s.map ∘ f) '' {x : P2 | ‖x‖ ∈ Icc a 1} = s.map '' b := by
    rw [image_comp,hb]
  have hwhole' : d i ∪ d i.rev = Sphere := by
    fin_cases i
    · exact hwhole
    · exact (union_comm _ _).trans hwhole
  have hinter' : d i ∩ d i.rev = r := by
    fin_cases i
    · exact hinter
    · exact (inter_comm _ _).trans hinter
  refine ⟨a,s.map ∘ f,E,ha,ha1,hsf,hsi.comp hfi hfS,
    fun x hx => hsimage.subset (mem_image_of_mem s.map (hfS hx)),hcompr,hother,?_,?_,?_,?_,?_,?_⟩
  · rw [hcompD,←image_union,hwhole',hsimage]
  · rw [hcompD,←hsi.image_inter (hdS i) (hdS i.rev),hinter',hcompr]
  · rw [hcompb]
    exact fun _ hx => (hbSO hx).2
  · intro x hx
    by_cases hxr : x ∈ (s.map ∘ f) '' rim
    · exact hR.frontier_subset (hrfront (hcompr.subset hxr))
    · exact interior_subset (hbin ⟨hcompb.subset hx,fun h => hxr (hcompr.symm.subset h)⟩)
  · rw [hcompb,hcompr]
    exact hbin
  · intro houtward P hP hPS hPR hmeet
    obtain ⟨l,U,hU,hrU,_,hl,_,_,hconfine⟩ :=
      s.exists_two_sided_rim_neighborhood d hd hwhole hinter hR hO hrO hrfront hisolate
        hinward houtward
    have hkS : k ⊆ Sphere := (subset_union_left.trans hkb.subset).trans (hdS i)
    have hkclosed : IsClosed (s.map '' k) := (hkp.isCompact.image_of_continuousOn
      (s.piecewiseAffine.continuousOn.mono hkS)).isClosed
    have hkdis : Disjoint (s.map '' k) (s.map '' r) := by
      apply disjoint_left.mpr
      rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,hyx⟩
      exact disjoint_left.mp hkr hx
        ((hsi ((hd 0).1.trans (hdS 0) hy) (hkS hx) hyx) ▸ hy)
    have hbR : s.map '' b ⊆ R := by
      intro x hx
      by_cases hr : x ∈ s.map '' r
      · exact hR.frontier_subset (hrfront hr)
      · exact interior_subset (hbin ⟨hx,hr⟩)
    have hil := s.disk_side_eq_of_inward_shell d hd hwhole hinter l i hU hrU hl
      hkclosed hkdis hkb hbR (hinward.mono inter_subset_left)
    rw [hcompD,hil]
    exact hconfine P hP hPS hPR hmeet

end PoincareConjecture.M76
