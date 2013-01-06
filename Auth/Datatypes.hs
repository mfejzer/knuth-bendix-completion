{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings,CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving, 
    MultiParamTypeClasses #-}

module Auth.Datatypes where
import Data.Data (Data, Typeable)

type Login = String
type Password = String

data User t = User {login::Login,password::Password,userContent::t,session::Maybe SessionHash}
    deriving (Eq, Ord, Read, Show, Data, Typeable)

data SessionHash = SessionHash {hash::String}
    deriving (Eq, Ord, Read, Show, Data, Typeable)

data AppStatusTemplate t = AppStatusTemplate {users::[User t]}
    deriving (Eq, Ord, Read, Show, Data, Typeable)

data LogInResult = SuccesfulLogIn SessionHash | NoSuchUser | WrongPassword 
    deriving (Eq, Ord, Read, Show, Data, Typeable)

data LogOutResult = SuccesfulLogOut | NoSuchSessionHash 
    deriving (Eq, Ord, Read, Show, Data, Typeable)

logIn ::Eq t=> AppStatusTemplate t -> Login -> Password ->SessionHash -> (LogInResult,AppStatusTemplate t)
logIn appStatus l p s = 
    if matchingUsers == []
      then (NoSuchUser,appStatus)
      else
        if (password matchingUser) /= p
          then (WrongPassword,appStatus)
          else (SuccesfulLogIn newSessionHash, AppStatusTemplate {users=restUsers++[matchingUser {session=Just newSessionHash}]})
    where 
    matchingUsers = filter (\u -> login u == l) (users appStatus)
    matchingUser = head matchingUsers
    restUsers = filter (\u -> login u /= l) (users appStatus)
    newSessionHash = s

logOut ::Eq t=> AppStatusTemplate t -> SessionHash -> (LogOutResult, AppStatusTemplate t)
logOut appStatus s = 
    if matchingUsers == []
      then (NoSuchSessionHash,appStatus)
      else (SuccesfulLogOut, AppStatusTemplate {users=restUsers++[matchingUser {session=newSessionHash}]})
    where 
    matchingUsers = filter (\u -> session u == Just s) (users appStatus)
    matchingUser = head matchingUsers
    restUsers = filter (\u -> session u /= Just s) (users appStatus)
    newSessionHash = Nothing


