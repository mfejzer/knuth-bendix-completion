{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings,CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving, 
    MultiParamTypeClasses #-}

module Auth where
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

data CheckHashResult = UserIsLogged | UserIsNotLogged
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

checkHash ::Eq t=> AppStatusTemplate t -> SessionHash -> CheckHashResult
checkHash appStatus sh = 
    if matchingUsers == []
      then UserIsNotLogged
      else UserIsLogged
    where 
    matchingUsers = filter (\u -> session u == Just sh) (users appStatus)
    matchingUser = head matchingUsers


logOut ::Eq t=> AppStatusTemplate t -> SessionHash -> (LogOutResult, AppStatusTemplate t)
logOut appStatus sh = 
    if matchingUsers == []
      then (NoSuchSessionHash,appStatus)
      else (SuccesfulLogOut, AppStatusTemplate {users=restUsers++[matchingUser {session=newSessionHash}]})
    where 
    matchingUsers = filter (\u -> session u == Just sh) (users appStatus)
    matchingUser = head matchingUsers
    restUsers = filter (\u -> session u /= Just sh) (users appStatus)
    newSessionHash = Nothing

updateUserContent :: Eq t => AppStatusTemplate t -> (t->t) -> SessionHash -> (Maybe t,AppStatusTemplate t)
updateUserContent appStatus f sh =
   if matchingUsers == []
      then (Nothing,appStatus)
      else (Just newUserContent,AppStatusTemplate {users=restUsers++[matchingUser {userContent=newUserContent}]})
    where 
    matchingUsers = filter (\u -> session u == Just sh) (users appStatus)
    matchingUser = head matchingUsers
    restUsers = filter (\u -> session u /= Just sh) (users appStatus)
    newUserContent = f (userContent matchingUser)

