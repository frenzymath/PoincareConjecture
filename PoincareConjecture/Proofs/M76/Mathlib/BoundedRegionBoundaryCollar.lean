import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionThinCollar
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization











set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]







theorem IsFinitePLBallPair.exists_protected_boundary_collar
    {B b d q : Set X} (hB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B (b ∪ d))
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q) (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hbd : b ∩ d = q) (K : SimplicialComplex ℝ X) (hK : K.faces.Finite)
    (hKB : K.space ⊆ B) (hKb : K.space ∩ b ⊆ q) :
    ∃ C e : Set X, C ⊆ B ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) C (b ∪ e) ∧
      IsFinitePLBallPair (ℝ × ℝ) e q ∧ b ∩ e = q ∧
      C ∩ d = q ∧ C ∩ K.space ⊆ q := by
  have hB' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B (d ∪ b) := by
    simpa only [union_comm] using hB
  have hdb : d ∩ b = q := (inter_comm _ _).trans hbd
  have hmodel := isFinitePLBallPair_halfBall (h := 1) (Or.inl rfl)
  obtain ⟨eb, heb, hebq⟩ := hb.exists_homeomorph isFinitePLBallPair_disk
  obtain ⟨H, hH, _, hHd, hHb⟩ := hB'.exists_extension_of_boundary_piece hmodel
    hd (isFinitePLBallPair_cap 1) hdb (cap_inter_disk one_ne_zero) eb heb hebq
  obtain ⟨f, hf, hfv⟩ := hH
  obtain ⟨g, hg, hgv⟩ := (show H.IsFinitePL from ⟨f, hf, hfv⟩).symm
  have hfinj : InjOn f B := by
    intro x hx y hy hxy
    have h : H ⟨x, hx⟩ = H ⟨y, hy⟩ :=
      Subtype.ext ((hfv ⟨x, hx⟩).trans (hxy.trans (hfv ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective h)
  have hginj : InjOn g (halfBall 1) := by
    intro x hx y hy hxy
    have h : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ :=
      Subtype.ext ((hgv ⟨x, hx⟩).trans (hxy.trans (hgv ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.symm.injective h)
  have hfg (p : (ℝ × ℝ) × ℝ) (hp : p ∈ halfBall 1) : f (g p) = p := by
    rw [← hgv ⟨p, hp⟩, ← hfv, H.apply_symm_apply]
  have hgf (x : X) (hx : x ∈ B) : g (f x) = x := by
    rw [← hfv ⟨x, hx⟩, ← hgv, H.symm_apply_apply]
  have himage (s : Set X) (t : Set ((ℝ × ℝ) × ℝ)) (hs : s ⊆ B)
      (ht : t ⊆ halfBall 1)
      (hmem : ∀ x : B, (x : X) ∈ s ↔ (H x : (ℝ × ℝ) × ℝ) ∈ t) :
      g '' t = s := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hm := (hmem (H.symm ⟨p, ht hp⟩)).mpr (by
        simpa only [H.apply_symm_apply] using hp)
      rwa [hgv] at hm
    · intro hx
      refine ⟨f x, ?_, hgf x (hs hx)⟩
      rw [← hfv ⟨x, hs hx⟩]
      exact (hmem ⟨x, hs hx⟩).mp hx
  have hgb : g '' disk = b := himage b disk
    (fun _ hx => hB.1 (Or.inl hx)) (fun _ hx => hmodel.1 (Or.inr hx)) hHb
  have hgd : g '' cap 1 = d := himage d (cap 1)
    (fun _ hx => hB.1 (Or.inr hx)) (fun _ hx => hmodel.1 (Or.inl hx)) hHd
  have hgr : g '' rim = q := by
    rw [← cap_inter_disk one_ne_zero,
      image_inter_on (fun x hx y hy hxy =>
        hginj (hmodel.1 (Or.inr hx)) (hmodel.1 (Or.inl hy)) hxy), hgd, hgb, hdb]
  obtain ⟨L, hL, hLK, hLf⟩ := hf.restrict K hK hKB
  have hLinj : InjOn f L.space := hfinj.mono (hLK.subset.trans hKB)
  let Q := hLf.embeddedImage hLinj
  have hQ : Q.faces.Finite := hLf.embeddedImage_finite hLinj hL
  have hQs : Q.space = f '' K.space := by
    rw [hLf.embeddedImage_space, hLK]
  have hQh : Q.space ⊆ halfBall 1 := by
    rw [hQs]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hfv ⟨x, hKB hx⟩]
    exact (H ⟨x, hKB hx⟩).property
  have hQd : Q.space ∩ disk ⊆ rim := by
    rintro p ⟨hpQ, hpd⟩
    obtain ⟨x, hx, rfl⟩ := hQs.subset hpQ
    have hxb : x ∈ b := (hHb ⟨x, hKB hx⟩).mpr (by rwa [hfv])
    have hxd : x ∈ d := hd.1 (hKb ⟨hx, hxb⟩)
    have hxcap : f x ∈ cap 1 := by
      rw [← hfv ⟨x, hKB hx⟩]
      exact (hHd ⟨x, hKB hx⟩).mp hxd
    exact (cap_inter_disk one_ne_zero).subset ⟨hxcap, hpd⟩
  obtain ⟨t, ht, havoid, hthin, hcap, hball⟩ :=
    exists_thinCollar_avoiding_polyhedron Q hQ hQh hQd
  have hcapt : cap t ⊆ halfBall 1 := fun _ hx => hthin (hball.1 (Or.inl hx))
  let C := g '' thinCollar t
  let e := g '' cap t
  have hCB : C ⊆ B := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← hgv ⟨p, hthin hp⟩]
    exact (H.symm ⟨p, hthin hp⟩).property
  have hCball : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) C (b ∪ e) := by
    have hh := hball.image_of_subset hg hthin hginj
    rw [image_union, hgb, union_comm] at hh
    exact hh
  have heball : IsFinitePLBallPair (ℝ × ℝ) e q := by
    have hh := (isFinitePLBallPair_cap t).image_of_subset hg hcapt hginj
    rwa [hgr] at hh
  have hbe : b ∩ e = q := by
    change b ∩ (g '' cap t) = q
    rw [← hgb, ← image_inter_on (fun x hx y hy hxy =>
      hginj (hcapt hx) (hmodel.1 (Or.inr hy)) hxy),
      inter_comm disk (cap t), cap_inter_disk ht.1.ne', hgr]
  have hCd : C ∩ d = q := by
    change (g '' thinCollar t) ∩ d = q
    rw [← hgd, ← image_inter_on (fun x hx y hy hxy =>
      hginj (hmodel.1 (Or.inl hx)) (hthin hy) hxy), hcap, hgr]
  refine ⟨C, e, hCB, hCball, heball, hbe, hCd, ?_⟩
  rintro x ⟨⟨p, hp, rfl⟩, hpK⟩
  have hpQ : p ∈ Q.space := hQs.symm.subset ⟨g p, hpK, hfg p (hthin hp)⟩
  exact hgr.subset ⟨p, havoid ⟨hpQ, hp⟩, rfl⟩

end Set
