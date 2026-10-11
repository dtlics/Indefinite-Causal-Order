import ICO.SupportProductRows.Row0
import ICO.SupportProductRows.Row1
import ICO.SupportProductRows.Row2
import ICO.SupportProductRows.Row3
import ICO.SupportProductRows.Row4
import ICO.SupportProductRows.Row5
import ICO.SupportProductRows.Row6
import ICO.SupportProductRows.Row7
import ICO.SupportProductRows.Row8
import ICO.SupportProductRows.Row9
import ICO.SupportProductRows.Row10
import ICO.SupportProductRows.Row11
import ICO.SupportProductRows.Row12
import ICO.SupportProductRows.Row13
import ICO.SupportProductRows.Row14
import ICO.SupportProductRows.Row15
import ICO.SupportProductRows.Row16
import ICO.SupportProductRows.Row17
import ICO.SupportProductRows.Row18
import ICO.SupportProductRows.Row19
import ICO.SupportProductRows.Row20
import ICO.SupportProductRows.Row21
import ICO.SupportProductRows.Row22
import ICO.SupportProductRows.Row23
import ICO.SupportProductRows.Row24
import ICO.SupportProductRows.Row25
import ICO.SupportProductRows.Row26
import ICO.SupportProductRows.Row27
import ICO.SupportProductRows.Row28
import ICO.SupportProductRows.Row29
import ICO.SupportProductRows.Row30
import ICO.SupportProductRows.Row31
import ICO.SupportProductRows.Row32
import ICO.SupportProductRows.Row33
import ICO.SupportProductRows.Row34
import ICO.SupportProductRows.Row35
import ICO.SupportProductRows.Row36
import ICO.SupportProductRows.Row37
import ICO.SupportProductRows.Row38
import ICO.SupportProductRows.Row39
import ICO.SupportProductRows.Row40
import ICO.SupportProductRows.Row41
import ICO.SupportProductRows.Row42
import ICO.SupportProductRows.Row43
import ICO.SupportProductRows.Row44
import ICO.SupportProductRows.Row45
import ICO.SupportProductRows.Row46
import ICO.SupportProductRows.Row47
import ICO.SupportProductRows.Row48
import ICO.SupportProductRows.Row49
import ICO.SupportProductRows.Row50
import ICO.SupportProductRows.Row51
import ICO.SupportProductRows.Row52
import ICO.SupportProductRows.Row53
import ICO.SupportProductRows.Row54
import ICO.SupportProductRows.Row55
import ICO.SupportProductRows.Row56
import ICO.SupportProductRows.Row57
import ICO.SupportProductRows.Row58
import ICO.SupportProductRows.Row59
import ICO.SupportProductRows.Row60
import ICO.SupportProductRows.Row61
import ICO.SupportProductRows.Row62
import ICO.SupportProductRows.Row63
import ICO.SupportProductRows.Row64
import ICO.SupportProductRows.Row65
import ICO.SupportProductRows.Row66
import ICO.SupportProductRows.Row67
import ICO.SupportProductRows.Row68
import ICO.SupportProductRows.Row69
import ICO.SupportProductRows.Row70
import ICO.SupportProductRows.Row71
import ICO.SupportProductRows.Row72
import ICO.SupportProductRows.Row73
import ICO.SupportProductRows.Row74
import ICO.SupportProductRows.Row75
import ICO.SupportProductRows.Row76
import ICO.SupportProductRows.Row77
import ICO.SupportProductRows.Row78
import ICO.SupportProductRows.Row79
import ICO.SupportProductRows.Row80
import ICO.SupportProductRows.Row81
import ICO.SupportProductRows.Row82
import ICO.SupportProductRows.Row83
import ICO.SupportProductRows.Row84
import ICO.SupportProductRows.Row85
import ICO.SupportProductRows.Row86
import ICO.SupportProductRows.Row87
import ICO.SupportProductRows.Row88
import ICO.SupportProductRows.Row89
import ICO.SupportProductRows.Row90
import ICO.SupportProductRows.Row91
import ICO.SupportProductRows.Row92
import ICO.SupportProductRows.Row93
import ICO.SupportProductRows.Row94
import ICO.SupportProductRows.Row95
import ICO.SupportProductRows.Row96
import ICO.SupportProductRows.Row97
import ICO.SupportProductRows.Row98
import ICO.SupportProductRows.Row99
import ICO.SupportProductRows.Row100
import ICO.SupportProductRows.Row101
import ICO.SupportProductRows.Row102
import ICO.SupportProductRows.Row103
import ICO.SupportProductRows.Row104
import ICO.SupportProductRows.Row105
import ICO.SupportProductRows.Row106
import ICO.SupportProductRows.Row107
import ICO.SupportProductRows.Row108
import ICO.SupportProductRows.Row109
import ICO.SupportProductRows.Row110
import ICO.SupportProductRows.Row111
import ICO.SupportProductRows.Row112
import ICO.SupportProductRows.Row113
import ICO.SupportProductRows.Row114
import ICO.SupportProductRows.Row115
import ICO.SupportProductRows.Row116
import ICO.SupportProductRows.Row117
import ICO.SupportProductRows.Row118
import ICO.SupportProductRows.Row119
import ICO.SupportProductRows.Row120
import ICO.SupportProductRows.Row121
import ICO.SupportProductRows.Row122
import ICO.SupportProductRows.Row123
import ICO.SupportProductRows.Row124
import ICO.SupportProductRows.Row125
import ICO.SupportProductRows.Row126
import ICO.SupportProductRows.Row127
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_product_entries (r c : Fin 128) :
    productEntry r.val c.val = if r.val = c.val then 1 else 0 := by
  match r with
  | ⟨0, _⟩ => exact product_row_0 c
  | ⟨1, _⟩ => exact product_row_1 c
  | ⟨2, _⟩ => exact product_row_2 c
  | ⟨3, _⟩ => exact product_row_3 c
  | ⟨4, _⟩ => exact product_row_4 c
  | ⟨5, _⟩ => exact product_row_5 c
  | ⟨6, _⟩ => exact product_row_6 c
  | ⟨7, _⟩ => exact product_row_7 c
  | ⟨8, _⟩ => exact product_row_8 c
  | ⟨9, _⟩ => exact product_row_9 c
  | ⟨10, _⟩ => exact product_row_10 c
  | ⟨11, _⟩ => exact product_row_11 c
  | ⟨12, _⟩ => exact product_row_12 c
  | ⟨13, _⟩ => exact product_row_13 c
  | ⟨14, _⟩ => exact product_row_14 c
  | ⟨15, _⟩ => exact product_row_15 c
  | ⟨16, _⟩ => exact product_row_16 c
  | ⟨17, _⟩ => exact product_row_17 c
  | ⟨18, _⟩ => exact product_row_18 c
  | ⟨19, _⟩ => exact product_row_19 c
  | ⟨20, _⟩ => exact product_row_20 c
  | ⟨21, _⟩ => exact product_row_21 c
  | ⟨22, _⟩ => exact product_row_22 c
  | ⟨23, _⟩ => exact product_row_23 c
  | ⟨24, _⟩ => exact product_row_24 c
  | ⟨25, _⟩ => exact product_row_25 c
  | ⟨26, _⟩ => exact product_row_26 c
  | ⟨27, _⟩ => exact product_row_27 c
  | ⟨28, _⟩ => exact product_row_28 c
  | ⟨29, _⟩ => exact product_row_29 c
  | ⟨30, _⟩ => exact product_row_30 c
  | ⟨31, _⟩ => exact product_row_31 c
  | ⟨32, _⟩ => exact product_row_32 c
  | ⟨33, _⟩ => exact product_row_33 c
  | ⟨34, _⟩ => exact product_row_34 c
  | ⟨35, _⟩ => exact product_row_35 c
  | ⟨36, _⟩ => exact product_row_36 c
  | ⟨37, _⟩ => exact product_row_37 c
  | ⟨38, _⟩ => exact product_row_38 c
  | ⟨39, _⟩ => exact product_row_39 c
  | ⟨40, _⟩ => exact product_row_40 c
  | ⟨41, _⟩ => exact product_row_41 c
  | ⟨42, _⟩ => exact product_row_42 c
  | ⟨43, _⟩ => exact product_row_43 c
  | ⟨44, _⟩ => exact product_row_44 c
  | ⟨45, _⟩ => exact product_row_45 c
  | ⟨46, _⟩ => exact product_row_46 c
  | ⟨47, _⟩ => exact product_row_47 c
  | ⟨48, _⟩ => exact product_row_48 c
  | ⟨49, _⟩ => exact product_row_49 c
  | ⟨50, _⟩ => exact product_row_50 c
  | ⟨51, _⟩ => exact product_row_51 c
  | ⟨52, _⟩ => exact product_row_52 c
  | ⟨53, _⟩ => exact product_row_53 c
  | ⟨54, _⟩ => exact product_row_54 c
  | ⟨55, _⟩ => exact product_row_55 c
  | ⟨56, _⟩ => exact product_row_56 c
  | ⟨57, _⟩ => exact product_row_57 c
  | ⟨58, _⟩ => exact product_row_58 c
  | ⟨59, _⟩ => exact product_row_59 c
  | ⟨60, _⟩ => exact product_row_60 c
  | ⟨61, _⟩ => exact product_row_61 c
  | ⟨62, _⟩ => exact product_row_62 c
  | ⟨63, _⟩ => exact product_row_63 c
  | ⟨64, _⟩ => exact product_row_64 c
  | ⟨65, _⟩ => exact product_row_65 c
  | ⟨66, _⟩ => exact product_row_66 c
  | ⟨67, _⟩ => exact product_row_67 c
  | ⟨68, _⟩ => exact product_row_68 c
  | ⟨69, _⟩ => exact product_row_69 c
  | ⟨70, _⟩ => exact product_row_70 c
  | ⟨71, _⟩ => exact product_row_71 c
  | ⟨72, _⟩ => exact product_row_72 c
  | ⟨73, _⟩ => exact product_row_73 c
  | ⟨74, _⟩ => exact product_row_74 c
  | ⟨75, _⟩ => exact product_row_75 c
  | ⟨76, _⟩ => exact product_row_76 c
  | ⟨77, _⟩ => exact product_row_77 c
  | ⟨78, _⟩ => exact product_row_78 c
  | ⟨79, _⟩ => exact product_row_79 c
  | ⟨80, _⟩ => exact product_row_80 c
  | ⟨81, _⟩ => exact product_row_81 c
  | ⟨82, _⟩ => exact product_row_82 c
  | ⟨83, _⟩ => exact product_row_83 c
  | ⟨84, _⟩ => exact product_row_84 c
  | ⟨85, _⟩ => exact product_row_85 c
  | ⟨86, _⟩ => exact product_row_86 c
  | ⟨87, _⟩ => exact product_row_87 c
  | ⟨88, _⟩ => exact product_row_88 c
  | ⟨89, _⟩ => exact product_row_89 c
  | ⟨90, _⟩ => exact product_row_90 c
  | ⟨91, _⟩ => exact product_row_91 c
  | ⟨92, _⟩ => exact product_row_92 c
  | ⟨93, _⟩ => exact product_row_93 c
  | ⟨94, _⟩ => exact product_row_94 c
  | ⟨95, _⟩ => exact product_row_95 c
  | ⟨96, _⟩ => exact product_row_96 c
  | ⟨97, _⟩ => exact product_row_97 c
  | ⟨98, _⟩ => exact product_row_98 c
  | ⟨99, _⟩ => exact product_row_99 c
  | ⟨100, _⟩ => exact product_row_100 c
  | ⟨101, _⟩ => exact product_row_101 c
  | ⟨102, _⟩ => exact product_row_102 c
  | ⟨103, _⟩ => exact product_row_103 c
  | ⟨104, _⟩ => exact product_row_104 c
  | ⟨105, _⟩ => exact product_row_105 c
  | ⟨106, _⟩ => exact product_row_106 c
  | ⟨107, _⟩ => exact product_row_107 c
  | ⟨108, _⟩ => exact product_row_108 c
  | ⟨109, _⟩ => exact product_row_109 c
  | ⟨110, _⟩ => exact product_row_110 c
  | ⟨111, _⟩ => exact product_row_111 c
  | ⟨112, _⟩ => exact product_row_112 c
  | ⟨113, _⟩ => exact product_row_113 c
  | ⟨114, _⟩ => exact product_row_114 c
  | ⟨115, _⟩ => exact product_row_115 c
  | ⟨116, _⟩ => exact product_row_116 c
  | ⟨117, _⟩ => exact product_row_117 c
  | ⟨118, _⟩ => exact product_row_118 c
  | ⟨119, _⟩ => exact product_row_119 c
  | ⟨120, _⟩ => exact product_row_120 c
  | ⟨121, _⟩ => exact product_row_121 c
  | ⟨122, _⟩ => exact product_row_122 c
  | ⟨123, _⟩ => exact product_row_123 c
  | ⟨124, _⟩ => exact product_row_124 c
  | ⟨125, _⟩ => exact product_row_125 c
  | ⟨126, _⟩ => exact product_row_126 c
  | ⟨127, _⟩ => exact product_row_127 c
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), h⟩ => omega

theorem product_entries_fin (r c : Fin 128) :
    productEntry r.val c.val = if r = c then 1 else 0 := by
  by_cases h : r = c
  · subst c
    simpa using all_product_entries r r
  · have hn : r.val ≠ c.val := fun hv => h (Fin.ext hv)
    simpa [h, hn] using all_product_entries r c

end ICO.SupportModularTree
