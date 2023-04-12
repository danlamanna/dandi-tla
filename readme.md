# Dandi TLA+ specs

## Prereqs
```sh
pip install tlacli
```

## Running

### assets scenario
```sh
tlacli check assets.tla --cfg assets.cfg --constant ASSETS "{a1, a2}" --constant NULL "NULL"
```

### versions scenario
```sh
tlacli check dandi.tla --cfg dandi.cfg --constant ASSETS "{a1}" --constant NULL "NULL"
```

## Resources
- https://www.youtube.com/watch?v=tqwcz-Yt9gQ
- https://learntla.com
- https://learntla.com/examples/index.html


