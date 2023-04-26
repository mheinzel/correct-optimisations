module Transformations where

import Language.Core
import Language.DeBruijn
import Language.CoDeBruijn
import Language.Generic
import Language.Generic.DeBruijn
import Language.Generic.CoDeBruijn

import Transformations.Recursion

import Transformations.DeBruijn.SubCtx
import Transformations.DeBruijn.Live
import Transformations.DeBruijn.StronglyLive  -- TODO: refactor, similar to Live
import Transformations.DeBruijn.DeadBindingDirect
import Transformations.DeBruijn.DeadBinding
import Transformations.DeBruijn.DeadBindingStrong  -- TODO: refactor, like DeadBindingEfficient
import Transformations.DeBruijn.DeadBindingEfficient  -- TODO: replace DeadBinding
import Transformations.DeBruijn.LetInward

import Transformations.CoDeBruijn.DeadBinding
import Transformations.CoDeBruijn.DeadBindingStrong
import Transformations.CoDeBruijn.LetInward

import Transformations.Generic.CoDeBruijn.DeadBinding
import Transformations.Generic.CoDeBruijn.DeadBindingStrong
