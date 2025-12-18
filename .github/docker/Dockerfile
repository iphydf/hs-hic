FROM toxchat/toktok-stack:haskell AS build

RUN ["rm", "-rf", "/work/hs-hic"]
COPY --chown=builder:users . /work/hs-hic
RUN ["stack", "install", "hic"]

FROM scratch
COPY --from=build /home/builder/.local/ /
